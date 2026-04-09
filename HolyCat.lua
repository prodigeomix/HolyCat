-- ============================================================
--  HolyCat v3.2.0 - Turtle WoW / SuperWoW Edition
--  State-machine Feral Druid DPS automation
--  Features: HUD, Auto-MCP, Bag Scanner, LoS Blacklist, True-Melee, 
--            Auto-Trinkets, Dynamic Clearcast Prioritization, Debugger
--  Optimized: Zero-Global, Pre-Cached Spells, Halved C-API Polling,
--             Zero-GC Loop Execution, C-API Hardware Snapshotting
-- ============================================================

local HS = {}

-- ============================================================
-- CONSTANTS & CONFIGURATION
-- ============================================================

HS.VERSION = "3.2.0"
HS.DEBUG_MAX_LINES = 500

-- DLL Presence Detection (Graceful Degradation)
local has_nampower = type(CastSpellByNameNoQueue) == "function"
local has_unitxp = type(UnitXP) == "function"
local has_superwow = type(SpellInfo) == "function"
local has_combat_reach = type(UnitCombatReach) == "function"

HS.STATE = { IDLE = 0, BUILDING = 1, FINISHING = 2, POWERSHIFTING = 3 }

-- GC Optimization: Memoize lowercasing to avoid allocation in hot loops
local _lowerCache = {}
local function FastLower(str)
    if not str then return "" end
    local l = _lowerCache[str]
    if not l then
        l = string.lower(str)
        _lowerCache[str] = l
    end
    return l
end

-- [RULE 8]: All texture constants string.lower() enforced to prevent Vanilla API case-mismatch
HS.TEXTURES = {
    RIP = FastLower("Ability_GhoulFrenzy"),
    RAKE = FastLower("Ability_Druid_Disembowel"),
    TIGER_FURY = FastLower("Ability_Mount_JungleTiger"),
    CLEARCAST = FastLower("Spell_Nature_CrystalBall"),
    BERSERK = FastLower("Ability_Druid_Berserk"),
    FAERIE_FIRE = FastLower("Spell_Nature_FaerieFire"),
    CAT_FORM = FastLower("Ability_Druid_CatForm"),
    PROWL = FastLower("Ability_Ambush"),
    POUNCE = FastLower("Ability_Druid_SupriseAttack"),
    MOTW = FastLower("Spell_Nature_Regeneration"),
}

HS.CC_TEXTURES = {
    FastLower("Spell_Nature_StrangleVines"),
    FastLower("Spell_Frost_FrostNova"),
    FastLower("Spell_Nature_EarthBind"),
    FastLower("Ability_Ensnare"),
}

HS.COSTS = { RAKE_BASE = 40, SHRED_BASE = 60, CLAW_BASE = 45, TIGER_FURY = 40, RIP = 30, BITE_MIN = 35, COWER = 20 }

HS.TIMING = {
    RAKE_REFRESH = 2.0,      
    BERSERK_LOCKOUT = 2.0,   
    BERSERK_COOLDOWN = 360,  
    POSITIONAL_LOCKOUT = 1.5,
    LOS_LOCKOUT = 3.0,       
    GLOBAL_DEBOUNCE = 0.25,  
    FINISHER_GRACE = 1.0,    
}

HS.ITEM_IDS = {
    healthstone = {
        [5512] = true, [5511] = true, [5510] = true,
        [9421] = true, [9422] = true, [9423] = true,
        [19013]= true, [19012]= true, [19011]= true,
    },
    mana = {
        [13444] = 6, -- Major Mana Potion
        [13443] = 5, -- Superior Mana Potion
        [6149]  = 4, -- Greater Mana Potion
        [3385]  = 3, -- Mana Potion
        [3384]  = 2, -- Lesser Mana Potion
        [118]   = 1, -- Minor Mana Potion
        [20520] = 7, -- Dark Rune
        [12662] = 7, -- Demonic Rune
    }
}

-- [RULE 1]: Zero Global Pollution. Localized strict state management.
local hsState = {
    catIdx = -1, -- Replaces UnitPowerType validation
    globalDebounce = 0, lastGCDTime = 0,
    combatStartTime = 0, combatEndTime = 0,
    positionalLockout = 0, losLockout = 0,
    lastAttackCmd = 0,
    mcpEquipped = false, mcpReady = false,
    currentDistance = nil, currentLoS = true,
    targetExists = false, targetDead = false,
    mcpCdStart = 0, mcpCdDuration = 0,
    t1CdStart = 0, t1CdDuration = 0,
    t2CdStart = 0, t2CdDuration = 0,

    -- Ability timing dict (replaces per-field lastXxxTime / xxxLockout vars)
    lastExecution = {},

    -- Buff state flags set by HSRebuildBuffCache (eliminates HSBuffCheck string.find on hot path)
    isClearcast = false, isBerserk = false,
    isTigerFury = false, isStealthed = false, hasMotw = false,

    -- Target debuff state set by HSUpdateTargetDebuffs (time-gated, 0.25 s interval)
    rakeActive = false, rakeExpiration = 0,
    targetRipExpiration = 0, targetBleedCount = 0,
    targetHasFaerieFire = false, lastTargetDebuffScan = 0,

    -- Optimistic client-side aura tracking
    rakeLocalExpiration = 0,
    ripLocalExpiration = 0,

    -- Distance / LoS result cache (0.1 s window, reduces UnitXP raycasting cost)
    lastDistanceUpdate = 0, cachedDistance = nil, cachedMeleeRange = 5.0,
    lastLoSCheck = 0, cachedHasLoS = true,
}

local hsCaches = {
    attackSlot = 0, spells = {}, talents = {},
    buffs = { dirty = true },
    items = { hp = nil, mana = nil },
    catForm = nil,
    gcdSpellIdx = nil,   -- cached reference spell index for GCD polling
}

-- Integer-flag buff texture cache: raw texture path -> integer flag, persists for the session.
-- Each unique texture is matched against all patterns exactly once, then the integer is reused.
local _buffTexCache = {}

local hsConfig = {
    usePowershift = false, useTigerFury = false, useBerserk = false, useCower = false, useFF = false,
    useMCP = true, useTrinkets = true, useItems = true, showHUD = true, itemHPThreshold = 0.20,
    useOpener = true, useAntiCC = true, useMotw = false,
    ffMaxCP = 2, rakeRefreshThreshold = 2.0, minManaShift = 800, debug = false,
    hudPos = nil 
}

-- GC-Optimized Ring Buffer for Debugging
local HSDebugLog = {}
local hsDebugHead = 1
local hsDebugCount = 0

-- ============================================================
-- UTILITY FUNCTIONS & DLL WRAPPERS
-- ============================================================

local function HSPrint(msg) 
    if DEFAULT_CHAT_FRAME then DEFAULT_CHAT_FRAME:AddMessage("|cffd08524[HS]|r " .. tostring(msg)) end 
end

local function HSDebug(tag, msg)
    if not hsConfig.debug then return end
    
    local logEntry = string.format("[%s] %s: %s", date("%H:%M:%S"), tag, tostring(msg))
    
    -- O(1) Ring buffer insertion
    HSDebugLog[hsDebugHead] = logEntry
    hsDebugHead = hsDebugHead + 1
    
    -- Wrap around
    if hsDebugHead > HS.DEBUG_MAX_LINES then 
        hsDebugHead = 1 
    end
    
    -- Track total up to max
    if hsDebugCount < HS.DEBUG_MAX_LINES then 
        hsDebugCount = hsDebugCount + 1 
    end
    
    HSPrint(logEntry)
end

local function ParseToggle(current, arg)
    if arg then arg = FastLower(arg) end
    if arg == "on" then return true end
    if arg == "off" then return false end
    return not current
end

local function HSRebuildBuffCache()
    -- Reset all buff state flags before scanning
    hsState.catIdx      = -1
    hsState.isClearcast = false
    hsState.isBerserk   = false
    hsState.isTigerFury = false
    hsState.isStealthed = false
    hsState.hasMotw     = false

    local i = 0
    -- Hard-cap at 32 to prevent infinite loops from malformed API responses
    while i <= 32 do
        local idx = GetPlayerBuff(i)
        if idx == -1 then break end
        local tex = GetPlayerBuffTexture(idx)
        if tex then
            -- Each texture is classified once per session via integer flag.
            -- Flags: 1=CatForm 2=Clearcast 3=Berserk 4=TigerFury 5=Prowl 6=MotW  -1=no match
            local flag = _buffTexCache[tex]
            if not flag then
                local lowerTex = FastLower(tex)
                flag = -1
                if     string.find(lowerTex, HS.TEXTURES.CAT_FORM,   1, true) then flag = 1
                elseif string.find(lowerTex, HS.TEXTURES.CLEARCAST,  1, true) then flag = 2
                elseif string.find(lowerTex, HS.TEXTURES.BERSERK,    1, true) then flag = 3
                elseif string.find(lowerTex, HS.TEXTURES.TIGER_FURY, 1, true) then flag = 4
                elseif string.find(lowerTex, HS.TEXTURES.PROWL,      1, true) then flag = 5
                elseif string.find(lowerTex, HS.TEXTURES.MOTW,       1, true) then flag = 6
                end
                _buffTexCache[tex] = flag
            end
            if     flag == 1 then hsState.catIdx      = idx
            elseif flag == 2 then hsState.isClearcast = true
            elseif flag == 3 then hsState.isBerserk   = true
            elseif flag == 4 then hsState.isTigerFury = true
            elseif flag == 5 then hsState.isStealthed = true
            elseif flag == 6 then hsState.hasMotw     = true
            end
        end
        i = i + 1
    end
    hsCaches.buffs.dirty = false
end

-- Integer-flag target debuff cache: raw texture path -> integer flag, persists session-long.
local _targetDebuffCache = {}

-- Scans all target debuffs and updates hsState debuff fields.
-- Called by HSCreateSnapshot on a 0.25 s timer to avoid rescanning 40 slots every keypress.
local function HSUpdateTargetDebuffs()
    hsState.rakeActive          = false
    hsState.rakeExpiration      = 0
    hsState.targetRipExpiration = 0
    hsState.targetBleedCount    = 0
    hsState.targetHasFaerieFire = false

    if not hsState.targetExists or hsState.targetDead then return end

    local now = GetTime()
    for i = 1, 40 do
        local a1, _, _, _, _, _, a7 = UnitDebuff("target", i)
        if not a1 then break end

        -- Flags: 1=Rake 2=Rip 3=Pounce(bleed) 4=FaerieFire  -1=no match
        local flag = _targetDebuffCache[a1]
        if not flag then
            local strTex = FastLower(tostring(a1))
            flag = -1
            if     string.find(strTex, HS.TEXTURES.RAKE,        1, true) then flag = 1
            elseif string.find(strTex, HS.TEXTURES.RIP,         1, true) then flag = 2
            elseif string.find(strTex, HS.TEXTURES.POUNCE,      1, true) then flag = 3
            elseif string.find(strTex, HS.TEXTURES.FAERIE_FIRE, 1, true) then flag = 4
            end
            _targetDebuffCache[a1] = flag
        end

        local expiration = tonumber(a7) or 0
        if flag == 1 then
            hsState.rakeActive       = true
            hsState.targetBleedCount = hsState.targetBleedCount + 1
            if expiration > now then hsState.rakeExpiration = expiration end
        elseif flag == 2 then
            hsState.targetBleedCount = hsState.targetBleedCount + 1
            if expiration > now then hsState.targetRipExpiration = expiration end
        elseif flag == 3 then
            hsState.targetBleedCount = hsState.targetBleedCount + 1
        elseif flag == 4 then
            hsState.targetHasFaerieFire = true
        end
    end
end

local function HSRebuildItemCache()
    hsCaches.items.hp = nil
    hsCaches.items.mana = nil
    local bestManaRank = 0
    
    for bag = 0, 4 do
        for slot = 1, GetContainerNumSlots(bag) do
            local link = GetContainerItemLink(bag, slot)
            if link then
                local _, _, idStr = string.find(link, "item:(%d+)")
                local id = tonumber(idStr)
                if id then
                    -- Get First Healthstone
                    if not hsCaches.items.hp and HS.ITEM_IDS.healthstone[id] then
                        hsCaches.items.hp = { bag = bag, slot = slot }
                    end
                    -- Get Highest Ranked Mana Item (Prioritizing Runes/Major Pots)
                    local rank = HS.ITEM_IDS.mana[id]
                    if rank and rank > bestManaRank then
                        hsCaches.items.mana = { bag = bag, slot = slot }
                        bestManaRank = rank
                    end
                end
            end
        end
    end
end

local function HSRebuildSpellCache()
    for k in pairs(hsCaches.spells) do hsCaches.spells[k] = nil end
    -- Bound the scan to the real spellbook size via GetSpellTabInfo instead of hardcoding 500.
    local numTabs = GetNumSpellTabs()
    if numTabs and numTabs > 0 then
        local _, _, offset, count = GetSpellTabInfo(numTabs)
        local total = (offset or 0) + (count or 0)
        for i = 1, total do
            local spellName = GetSpellName(i, "spell")
            if spellName then hsCaches.spells[spellName] = i end
        end
    else
        -- Fallback for edge-case where spellbook tab info is unavailable
        for i = 1, 500 do
            local spellName = GetSpellName(i, "spell")
            if spellName then hsCaches.spells[spellName] = i end
        end
    end
    -- Cache GCD reference spell: Claw/Shred/Rake have no personal CD beyond GCD,
    -- so GetSpellCooldown on them is unambiguously the server's shared GCD timer.
    hsCaches.gcdSpellIdx = hsCaches.spells["Claw"] or hsCaches.spells["Shred"] or hsCaches.spells["Rake"]
end

local function HSCacheShapeshift()
    hsCaches.catForm = nil
    for i = 1, GetNumShapeshiftForms() do
        local tex = GetShapeshiftFormInfo(i)
        if tex and string.find(FastLower(tex), HS.TEXTURES.CAT_FORM, 1, true) then 
            hsCaches.catForm = i 
            break 
        end
    end
end

local function HSGetSpellIndex(name) return hsCaches.spells[name] end
local function HSHasSpell(name) return hsCaches.spells[name] ~= nil end

local function HSSpellCooldown(name)
    local idx = HSGetSpellIndex(name)
    if not idx then return 999 end
    local start, duration = GetSpellCooldown(idx, "spell")
    if not start or start == 0 then return 0 end
    local remain = (start + duration) - GetTime()
    return remain > 0 and remain or 0
end

local function HSCastSpell(name)
    local idx = HSGetSpellIndex(name)
    if idx then
        if has_nampower then
            local sName, sRank = GetSpellName(idx, "spell")
            local castStr = sName
            -- Shield against Vanilla API parenthesis weirdness via Nampower
            if sRank and sRank ~= "" then castStr = sName .. "(" .. sRank .. ")" end
            CastSpellByNameNoQueue(castStr)
        else
            CastSpell(idx, "spell")
        end
        HSDebug("CAST", name)
        return true
    end
    return false
end

local function HSUseEmergencyItem(snapshot)
    if (snapshot.now - (hsState.lastExecution["Item"] or 0)) < 5.0 then return false end

    if snapshot.playerHP <= hsConfig.itemHPThreshold and hsCaches.items.hp then
        local b, s = hsCaches.items.hp.bag, hsCaches.items.hp.slot
        local start, dur = GetContainerItemCooldown(b, s)
        if start == 0 or dur <= 1.5 then 
            UseContainerItem(b, s) 
            HSDebug("ITEM", "Used Cached HP Item") 
            return true 
        end
    end
    if snapshot.hasSuperWoW and snapshot.mana < hsConfig.minManaShift and hsCaches.items.mana then
        local b, s = hsCaches.items.mana.bag, hsCaches.items.mana.slot
        local start, dur = GetContainerItemCooldown(b, s)
        if start == 0 or dur <= 1.5 then 
            UseContainerItem(b, s) 
            HSDebug("ITEM", "Used Cached Mana Item") 
            return true 
        end
    end
    return false
end

local function HSBuildActionCache()
    hsCaches.attackSlot = 0
    for i = 1, 120 do 
        if IsAttackAction(i) then 
            hsCaches.attackSlot = i 
            break 
        end 
    end
end

local function HSLoadTalents()
    local _, classToken = UnitClass("player")
    if classToken ~= "DRUID" then return end
    
    for i = 1, GetNumTalents(2) do
        local name, _, _, _, rank = GetTalentInfo(2, i)
        if name then
            local lname = FastLower(name)
            if lname == "ferocity" then hsCaches.talents.ferocity = rank
            elseif lname == "improved shred" then hsCaches.talents.improvedShred = rank
            elseif lname == "open wounds" then hsCaches.talents.openWounds = rank
            elseif lname == "carnage" then hsCaches.talents.carnage = rank
            end
        end
    end
end

local function HSGetEnergyCost(spellType)
    local t = hsCaches.talents
    if spellType == "Rake" then return HS.COSTS.RAKE_BASE - (t.ferocity or 0)
    -- Improved Shred max is 2 points for 12 energy in Vanilla/Turtle
    elseif spellType == "Shred" then return HS.COSTS.SHRED_BASE - ((t.improvedShred or 0) * 6)
    elseif spellType == "Claw" then return HS.COSTS.CLAW_BASE - (t.ferocity or 0) end
    return 0
end

local function HSGetDruidMana()
    local power, realMana = UnitMana("player")
    local maxMana = math.max(1, UnitManaMax("player"))
    if type(realMana) == "number" then return realMana, maxMana, true end
    return power, maxMana, false
end

local function HSUpdatePositionState(ev, a1)
    a1 = a1 or ""
    if ev == "CHAT_MSG_SPELL_SELF_DAMAGE" then
        local a1L = FastLower(a1)
        if string.find(a1L, "your shred", 1, true) then hsState.positionalLockout = 0 end
        if string.find(a1L, "fail", 1, true) or string.find(a1L, "dodge", 1, true) or string.find(a1L, "miss", 1, true) or string.find(a1L, "parry", 1, true) then
            hsState.rakeLocalExpiration = 0
            hsState.ripLocalExpiration = 0
        end
    elseif ev == "UI_ERROR_MESSAGE" then
        local a1L = FastLower(a1)
        if string.find(a1L, "behind", 1, true) or string.find(a1L, "facing", 1, true) then
            hsState.positionalLockout = GetTime() + HS.TIMING.POSITIONAL_LOCKOUT
            hsState.lastGCDTime = 0
            hsState.rakeLocalExpiration = 0
            hsState.ripLocalExpiration = 0
        elseif string.find(a1L, "line of sight", 1, true) then
            hsState.losLockout = GetTime() + HS.TIMING.LOS_LOCKOUT
            hsState.lastGCDTime = 0
            hsState.rakeLocalExpiration = 0
            hsState.ripLocalExpiration = 0
        elseif string.find(a1L, "out of range", 1, true) or string.find(a1L, "too far", 1, true) then
            -- Soft-debounce to prevent infinite log spam when riding the edge of a hitbox
            hsState.lastGCDTime = GetTime() - 0.35
            hsState.rakeLocalExpiration = 0
            hsState.ripLocalExpiration = 0
        end
    elseif ev == "PLAYER_TARGET_CHANGED" then
        hsState.positionalLockout = 0
        hsState.losLockout = 0
        hsState.targetExists = UnitExists("target") and true or false
        hsState.targetDead = hsState.targetExists and (UnitIsDead("target") and true or false) or false
        hsState.rakeLocalExpiration = 0
        hsState.ripLocalExpiration = 0
    end
end

local function HSUpdateEquipmentCooldowns()
    if hsState.mcpEquipped then
        local st, dur = GetInventoryItemCooldown("player", 16)
        hsState.mcpCdStart = st or 0
        hsState.mcpCdDuration = dur or 0
    end
    
    local st1, dur1 = GetInventoryItemCooldown("player", 13)
    hsState.t1CdStart = st1 or 0
    hsState.t1CdDuration = dur1 or 0
    
    local st2, dur2 = GetInventoryItemCooldown("player", 14)
    hsState.t2CdStart = st2 or 0
    hsState.t2CdDuration = dur2 or 0
end

local function HSUpdateMCPState()
    local link = GetInventoryItemLink("player", 16)
    hsState.mcpEquipped = (link and string.find(link, "Manual Crowd Pummeler", 1, true)) and true or false
    HSUpdateEquipmentCooldowns()
end

-- ============================================================
-- SNAPSHOT CREATION 
-- ============================================================
-- GC Optimization: Pre-allocate snapshot table and reuse it to prevent 
-- generation of orphaned tables on the hot path.
local hsSnapshot = {}

local function HSCreateSnapshot()
    -- Always rebuild aura flags first if the player state changed
    if hsCaches.buffs.dirty then HSRebuildBuffCache() end

    local now = GetTime()
    local energy = UnitMana("player")
    local mana, maxMana, hasSuperWoW = HSGetDruidMana()
    local cp = GetComboPoints() or 0
    
    local inCombat = (UnitAffectingCombat("player") and true or false)
    local targetExists = hsState.targetExists
    local targetDead = hsState.targetDead
    local targetInCombat = targetExists and (UnitAffectingCombat("target") and true or false) or false
    
    local playerHP = UnitHealth("player") / math.max(1, UnitHealthMax("player"))
    local targetHP = 0
    
    if targetExists and not targetDead then
        if has_nampower and type(GetUnitField) == "function" then
            local ok, hp, maxHp = pcall(function() 
                return GetUnitField("target", "health"), GetUnitField("target", "maxHealth") 
            end)
            if ok and type(hp) == "number" and type(maxHp) == "number" and maxHp > 0 then
                targetHP = hp / maxHp
            else
                targetHP = UnitHealth("target") / math.max(1, UnitHealthMax("target"))
            end
        else
            targetHP = UnitHealth("target") / math.max(1, UnitHealthMax("target"))
        end
    end
    
    local inMelee = false
    local hasLoS = true

    if targetExists and not targetDead then
        if has_unitxp then
            -- Cache UnitXP distance/LoS results (0.1 s window) to reduce raycasting cost.
            if (now - hsState.lastDistanceUpdate) > 0.1 then
                local sDist, dist = pcall(UnitXP, "distanceBetween", "player", "target")
                if sDist and type(dist) == "number" then
                    hsState.cachedDistance = dist
                    if has_combat_reach then
                        local pReach = UnitCombatReach("player") or 1.5
                        local tReach = UnitCombatReach("target") or 1.5
                        hsState.cachedMeleeRange = math.max(5.0, pReach + tReach + 1.33)
                    else
                        hsState.cachedMeleeRange = 5.0
                    end
                else
                    hsState.cachedDistance = nil
                end
                hsState.lastDistanceUpdate = now
            end

            if hsState.cachedDistance then
                hsState.currentDistance = hsState.cachedDistance
                inMelee = (hsState.cachedDistance <= hsState.cachedMeleeRange)
            else
                hsState.currentDistance = nil
                inMelee = (CheckInteractDistance("target", 3) == 1)
            end

            if (now - hsState.lastLoSCheck) > 0.1 then
                local sLoS, sight = pcall(UnitXP, "inSight", "player", "target")
                if sLoS and type(sight) == "boolean" then
                    hsState.cachedHasLoS = sight
                    hsState.currentLoS   = sight
                else
                    hsState.cachedHasLoS = true
                    hsState.currentLoS   = true
                end
                hsState.lastLoSCheck = now
            end
            hasLoS = (hsState.losLockout == 0 or now > hsState.losLockout) and hsState.cachedHasLoS
        else
            hsState.currentDistance = nil
            inMelee = (CheckInteractDistance("target", 3) == 1)
            hasLoS  = (hsState.losLockout == 0 or now > hsState.losLockout)
            hsState.currentLoS = hasLoS
        end
    end
    
    local canShred = inMelee and (hsState.positionalLockout == 0 or now > hsState.positionalLockout)
    local isBoss = false
    
    if targetExists then
        local lvl = UnitLevel("target")
        local class = UnitClassification("target")
        if lvl == -1 or class == "worldboss" then isBoss = true end
    end
    
    local isStealthed = hsState.isStealthed
    local isRooted = false
    for i = 1, 16 do
        local tex = UnitDebuff("player", i)
        if not tex then break end
        local ltex = FastLower(tex)
        for _, ccTex in ipairs(HS.CC_TEXTURES) do
            if string.find(ltex, ccTex, 1, true) then
                isRooted = true
                break
            end
        end
    end
    
    -- Time-gated target debuff scan: rescans at most every 0.25 s instead of every keypress.
    if (now - hsState.lastTargetDebuffScan) > 0.25 then
        HSUpdateTargetDebuffs()
        hsState.lastTargetDebuffScan = now
    end

    local rakeRemaining, ripRemaining = 0, 0
    if targetExists and not targetDead then
        -- Rake timing from server scan (with optimistic client fallback)
        if hsState.rakeExpiration > now then
            rakeRemaining = hsState.rakeExpiration - now
        elseif hsState.rakeActive then
            rakeRemaining = 999  -- active but no server expiration data
        end
        if rakeRemaining == 0 and hsState.rakeLocalExpiration > now then
            rakeRemaining = hsState.rakeLocalExpiration - now
            hsState.rakeActive = true
        end
        -- Rip timing
        if hsState.targetRipExpiration > now then
            ripRemaining = hsState.targetRipExpiration - now
        end
        if ripRemaining == 0 and hsState.ripLocalExpiration > now then
            ripRemaining = hsState.ripLocalExpiration - now
        end
    end

    hsState.mcpReady = false
    if hsState.mcpEquipped then
        hsState.mcpReady = (hsState.mcpCdStart == 0 or (now >= (hsState.mcpCdStart + hsState.mcpCdDuration) - 1.5))
    end

    local t1Ready, t2Ready = false, false
    if hsConfig.useTrinkets and inCombat and isBoss then
        t1Ready = (hsState.t1CdStart == 0 or (now >= (hsState.t1CdStart + hsState.t1CdDuration) - 1.5))
        t2Ready = (hsState.t2CdStart == 0 or (now >= (hsState.t2CdStart + hsState.t2CdDuration) - 1.5))
    end

    local gcdRemain = 0
    if has_nampower then
        -- Nampower queues spells up to ~400 ms before the GCD expires, making
        -- GetSpellCooldown return stale client-side state.  Use virtualGCD only.
        local elapsed = now - hsState.lastGCDTime
        if elapsed >= 0 then
            gcdRemain = 1.5 - elapsed
            gcdRemain = gcdRemain > 0 and gcdRemain or 0
        end
    else
        -- Layer 1: server-authoritative read via cached GCD reference spell.
        local refSpell = hsCaches.gcdSpellIdx
        if refSpell then
            local st, dur = GetSpellCooldown(refSpell, "spell")
            if st and st > 0 and dur > 0 then
                local r = (st + dur) - now
                gcdRemain = r > 0 and r or 0
            end
        end
        -- Layer 2: virtual GCD fallback (covers any spell that isn't the ref spell).
        local virtualGcdRemain = 0.85 - (now - hsState.lastGCDTime)
        if virtualGcdRemain > gcdRemain then
            gcdRemain = virtualGcdRemain
        end
    end

    -- Mutate existing hsSnapshot instead of reallocating memory
    hsSnapshot.now = now
    hsSnapshot.energy = energy
    hsSnapshot.mana = mana
    hsSnapshot.maxMana = maxMana
    hsSnapshot.hasSuperWoW = hasSuperWoW
    hsSnapshot.comboPoints = cp
    hsSnapshot.inCombat = inCombat
    hsSnapshot.targetInCombat = targetInCombat
    hsSnapshot.playerHP = playerHP
    hsSnapshot.targetExists = targetExists
    hsSnapshot.targetDead = targetDead
    hsSnapshot.targetHP = targetHP
    hsSnapshot.inMelee = inMelee
    hsSnapshot.canShred = canShred
    hsSnapshot.isStealthed = isStealthed
    hsSnapshot.isRooted = isRooted
    hsSnapshot.bleedCount = hsState.targetBleedCount
    hsSnapshot.hasLoS = hasLoS
    hsSnapshot.isBoss = isBoss
    hsSnapshot.hasClearcast = hsState.isClearcast
    hsSnapshot.hasBerserk   = hsState.isBerserk
    hsSnapshot.hasTigerFury = hsState.isTigerFury
    hsSnapshot.rakeRemaining = rakeRemaining
    hsSnapshot.ripRemaining = ripRemaining
    hsSnapshot.hasFaerieFire = hsState.targetHasFaerieFire
    local le = hsState.lastExecution
    hsSnapshot.timeSinceBerserk   = le["Berserk"]     and (now - le["Berserk"])     or 999
    hsSnapshot.timeSinceTigerFury = le["Tiger's Fury"] and (now - le["Tiger's Fury"]) or 999
    hsSnapshot.timeSinceFinisher  = le["Finisher"]    and (now - le["Finisher"])    or 999
    hsSnapshot.inParty = GetNumPartyMembers() > 0
    hsSnapshot.isTargetingPlayer = (targetExists and UnitIsUnit("targettarget", "player")) and true or false
    hsSnapshot.mcpReady = hsState.mcpReady
    hsSnapshot.t1Ready = t1Ready
    hsSnapshot.t2Ready = t2Ready
    hsSnapshot.gcd = gcdRemain

    return hsSnapshot
end

-- ============================================================
-- DECISION TABLE 
-- ============================================================

local HSDecisions = {
    {
        id = "Anti-CC",
        check = function(s)
            if s.gcd > 0.05 then return false end
            if not hsConfig.useAntiCC or not s.isRooted then return false end
            return s.hasSuperWoW and s.mana >= hsConfig.minManaShift
        end, score = 300,
    },
    {
        id = "Emergency Item",
        check = function(s)
            if not hsConfig.useItems or not s.inCombat then return false end
            return s.playerHP <= hsConfig.itemHPThreshold or (s.hasSuperWoW and s.mana < hsConfig.minManaShift)
        end, score = 200,
    },
    {
        id = "Manual Crowd Pummeler",
        check = function(s)
            if not hsConfig.useMCP or not s.inCombat or not s.isBoss or not hsState.mcpEquipped then return false end
            if (s.now - (hsState.lastExecution["MCP"] or 0)) < 2.0 then return false end
            return s.mcpReady
        end, score = 195,
    },
    {
        id = "Trinkets",
        check = function(s)
            if not hsConfig.useTrinkets or not s.inCombat or not s.isBoss then return false end
            if (s.now - (hsState.lastExecution["Trinket"] or 0)) < 5.0 then return false end
            return s.t1Ready or s.t2Ready
        end, score = 194,
    },
    {
        id = "Berserk",
        check = function(s)
            if s.gcd > 0.05 then return false end
            if not hsConfig.useBerserk or not HSHasSpell("Berserk") or not s.inMelee or s.hasBerserk or not s.hasLoS then return false end
            if s.timeSinceBerserk < HS.TIMING.BERSERK_LOCKOUT or s.timeSinceBerserk < HS.TIMING.BERSERK_COOLDOWN then return false end
            return s.comboPoints >= 4 or (s.energy < 50 and HSSpellCooldown("Tiger's Fury") > 0)
        end, score = 95,
    },
    {
        id = "Tiger's Fury",
        check = function(s)
            if s.gcd > 0.05 then return false end
            if not hsConfig.useTigerFury or not HSHasSpell("Tiger's Fury") or not s.inCombat or s.comboPoints >= 4 or s.hasTigerFury then return false end
            if s.timeSinceTigerFury < 1.0 or HSSpellCooldown("Tiger's Fury") > 0 then return false end
            return s.energy >= HS.COSTS.TIGER_FURY
        end, score = 90,
    },
    {
        id = "Shred",
        check = function(s)
            if s.gcd > 0.05 then return false end
            if not s.inMelee or not s.hasLoS or not s.canShred or s.comboPoints >= 5 then return false end
            return s.energy >= HSGetEnergyCost("Shred") or s.hasClearcast
        end, score = function(s) return s.hasClearcast and 85 or 60 end, 
    },
    {
        id = "Claw",
        check = function(s)
            if s.gcd > 0.05 then return false end
            if not s.inMelee or not s.hasLoS or s.comboPoints >= 5 then return false end
            return s.energy >= HSGetEnergyCost("Claw") or s.hasClearcast
        end, score = function(s) return s.hasClearcast and 84 or 50 end, 
    },
    {
        id = "Cower",
        check = function(s)
            if s.gcd > 0.05 then return false end
            if not hsConfig.useCower or not HSHasSpell("Cower") or not s.inParty or not s.inCombat then return false end
            if not s.hasLoS or not s.isTargetingPlayer then return false end
            if HSSpellCooldown("Cower") > 0 then return false end
            return s.energy >= HS.COSTS.COWER
        end, score = 83,
    },
    {
        id = "Ravage",
        check = function(s)
            if s.gcd > 0.05 then return false end
            if not hsConfig.useOpener or not s.isStealthed or not s.inMelee or not s.canShred then return false end
            if (hsCaches.talents.openWounds or 0) > 0 then return false end
            return s.energy >= 60
        end, score = 100,
    },
    {
        id = "Pounce",
        check = function(s)
            if s.gcd > 0.05 then return false end
            if not hsConfig.useOpener or not s.isStealthed or not s.inMelee then return false end
            return s.energy >= 50
        end, score = 95,
    },
    {
        id = "Rake",
        check = function(s)
            if s.gcd > 0.05 then return false end
            if not s.inMelee or not s.hasLoS or s.comboPoints >= 5 then return false end
            
            if (hsCaches.talents.openWounds or 0) > 0 and s.bleedCount == 0 then
                return s.energy >= HSGetEnergyCost("Rake") or s.hasClearcast
            end
            
            if s.comboPoints >= 4 or s.rakeRemaining > hsConfig.rakeRefreshThreshold then return false end
            return s.energy >= HSGetEnergyCost("Rake") or s.hasClearcast
        end, score = function(s) return ((hsCaches.talents.openWounds or 0) > 0 and s.bleedCount == 0) and 92 or 80 end,
    },
    {
        id = "Faerie Fire (Feral)",
        check = function(s)
            if s.gcd > 0.05 then return false end
            if not hsConfig.useFF or not HSHasSpell("Faerie Fire (Feral)") or not s.targetExists or s.targetDead or not s.hasLoS then return false end
            if s.comboPoints > hsConfig.ffMaxCP or HSSpellCooldown("Faerie Fire (Feral)") > 0 then return false end
            
            if not s.inMelee and not s.targetInCombat then return false end
            return not s.hasFaerieFire
        end, score = 75,
    },
    {
        id = "Rip",
        check = function(s)
            if s.gcd > 0.05 then return false end
            if s.timeSinceFinisher < 2.0 then return false end
            if not s.hasLoS or s.comboPoints < 5 or s.ripRemaining > 0 then return false end
            
            local hpFloor = s.isBoss and 0.0 or 0.15
            if s.targetHP < hpFloor then return false end
            
            return s.energy >= HS.COSTS.RIP or s.hasClearcast
        end, score = 40,
    },
    {
        id = "Ferocious Bite",
        check = function(s)
            if s.gcd > 0.05 then return false end
            if not s.hasLoS then return false end
            if s.timeSinceFinisher < 2.0 then return false end
            
            local isDyingTrash = not s.isBoss and s.targetHP > 0 and s.targetHP < 0.15
            
            if isDyingTrash then
                if s.comboPoints < 3 then return false end
            else
                if s.comboPoints < 5 then return false end
            end
            
            return s.hasClearcast or s.energy >= HS.COSTS.BITE_MIN
        end, score = 30,
    },
    {
        id = "Powershift",
        check = function(s)
            if s.gcd > 0.05 then return false end
            if not hsConfig.usePowershift or not s.hasSuperWoW or not s.inCombat then return false end 
            if s.mana < hsConfig.minManaShift or s.hasClearcast or s.energy >= 40 then return false end
            return s.timeSinceFinisher >= HS.TIMING.FINISHER_GRACE
        end, score = 20,
    },
}

-- ============================================================
-- EXECUTION ENGINE
-- ============================================================

local function HSExecute(actionId, snapshot)
    local success = false
    HSDebug("EXEC", actionId)
    
    local le = hsState.lastExecution
    if actionId == "Emergency Item" then
        success = HSUseEmergencyItem(snapshot)
        if success then le["Item"] = snapshot.now; HSUpdateEquipmentCooldowns() end
    elseif actionId == "Manual Crowd Pummeler" then
        UseInventoryItem(16)
        le["MCP"] = snapshot.now
        HSUpdateEquipmentCooldowns()
        success = true
    elseif actionId == "Trinkets" then
        if snapshot.t1Ready then UseInventoryItem(13) end
        if snapshot.t2Ready then UseInventoryItem(14) end
        le["Trinket"] = snapshot.now
        HSUpdateEquipmentCooldowns()
    elseif actionId == "Powershift" or actionId == "Anti-CC" then
        if hsCaches.catForm then
            CastShapeshiftForm(hsCaches.catForm)
            le["Finisher"] = snapshot.now
            hsState.lastGCDTime = snapshot.now
            success = true
        end
    elseif actionId == "Tiger's Fury" then
        if HSCastSpell("Tiger's Fury") then
            le["Tiger's Fury"] = snapshot.now
            hsState.lastGCDTime = snapshot.now
            success = true
        end
    elseif actionId == "Berserk" then
        if HSCastSpell("Berserk") then
            le["Berserk"] = snapshot.now
            hsState.lastGCDTime = snapshot.now
            success = true
        end
    elseif actionId == "Rake" then
        if HSCastSpell("Rake") then
            le["Rake"] = snapshot.now
            hsState.lastGCDTime = snapshot.now
            hsState.rakeLocalExpiration = snapshot.now + 9.0
            success = true
        end
    elseif actionId == "Rip" or actionId == "Ferocious Bite" then
        if HSCastSpell(actionId) then
            le["Finisher"] = snapshot.now
            hsState.lastGCDTime = snapshot.now
            if actionId == "Rip" then
                hsState.ripLocalExpiration = snapshot.now + 12.0
            end
            success = true
        end
    else
        success = HSCastSpell(actionId)
        if success and (actionId == "Shred" or actionId == "Claw" or actionId == "Cower" or actionId == "Faerie Fire (Feral)") then
            hsState.lastGCDTime = snapshot.now
        end
    end
    
    if success then hsState.globalDebounce = GetTime() + HS.TIMING.GLOBAL_DEBOUNCE end
    return success
end

local function HSAssistTank()
    if GetNumPartyMembers() == 0 then return end
    for i = 1, 4 do
        local partyUnit = "party" .. i
        if UnitExists(partyUnit) and UnitIsConnected(partyUnit) then
            local targetUnit = partyUnit .. "target"
            local exists, guid = UnitExists(targetUnit)
            exists = exists and true or false
            if exists and not (UnitIsDead(targetUnit) and true or false) and UnitCanAttack("player", targetUnit) then
                
                local inRange = false
                if has_unitxp then
                    local sDist, dist = pcall(UnitXP, "distanceBetween", "player", targetUnit)
                    if sDist and type(dist) == "number" then
                        local meleeRange = 5.0
                        if has_combat_reach then
                            local pReach = UnitCombatReach("player") or 1.5
                            local tReach = UnitCombatReach(targetUnit) or 1.5
                            meleeRange = math.max(5.0, pReach + tReach + 1.33)
                        end
                        inRange = (dist <= meleeRange)
                    else
                        inRange = (CheckInteractDistance(targetUnit, 3) == 1)
                    end
                else
                    inRange = (CheckInteractDistance(targetUnit, 3) == 1)
                end
                
                if inRange then
                    if has_superwow and guid and hsConfig.useFF and HSHasSpell("Faerie Fire (Feral)") and HSSpellCooldown("Faerie Fire (Feral)") == 0 then
                        if (UnitAffectingCombat(targetUnit) and true or false) then
                            local oldSound = PlaySound; PlaySound = function() end
                            CastSpellByName("Faerie Fire (Feral)", guid)
                            PlaySound = oldSound
                            HSDebug("ASSIST", "SuperWoW GUID Cast: Faerie Fire on " .. targetUnit)
                        end
                    end
                    
                    local oldSound = PlaySound; PlaySound = function() end
                    TargetUnit(targetUnit)
                    PlaySound = oldSound
                    return
                end
            end
        end
    end
end

local function HolyCat_CommandDPS()
    if hsCaches.buffs.dirty then HSRebuildBuffCache() end

    local now = GetTime()
    local isCat = (hsState.catIdx >= 0)
    local outOfCombatForAwhile = not UnitAffectingCombat("player") and (hsState.combatEndTime == 0 or (now - hsState.combatEndTime) > 3.0)

    -- Auto-Buff: Mark of the Wild
    if hsConfig.useMotw and outOfCombatForAwhile and HSHasSpell("Mark of the Wild") then
        if not HSBuffCheck(HS.TEXTURES.MOTW) then
            if not isCat then
                local currentMana = UnitMana("player")
                -- Unconditionally return while waiting for GCD or aura sync
                if currentMana >= 120 then
                    if HSSpellCooldown("Mark of the Wild") == 0 then
                        HSCastSpell("Mark of the Wild")
                    end
                    return
                end
            else
                local realMana, _, hasSuperWoW = HSGetDruidMana()
                if hasSuperWoW and realMana > hsConfig.minManaShift then
                    CancelPlayerBuff(hsState.catIdx)
                    hsCaches.buffs.dirty = true
                    return
                end
            end
        end
    end

    -- Form Validation Safety via catIdx (Avoids UnitPowerType stale issues)
    if hsState.catIdx < 0 then
        if hsCaches.catForm then CastShapeshiftForm(hsCaches.catForm) end
        return
    end
    
    if not UnitExists("target") or (UnitIsDead("target") and true or false) then
        local oldSound = PlaySound; PlaySound = function() end
        TargetNearestEnemy()
        PlaySound = oldSound
        if not UnitExists("target") or (UnitIsDead("target") and true or false) then HSAssistTank(); return end
    end
    
    if now < hsState.globalDebounce then return end
    local snapshot = HSCreateSnapshot()
    
    local bestScore, bestDecision = 0, nil
    local len = table.getn(HSDecisions)
    for i = 1, len do
        local decision = HSDecisions[i]
        local dScore = type(decision.score) == "function" and decision.score(snapshot) or decision.score
        if decision.check(snapshot) and dScore > bestScore then
            bestScore = dScore
            bestDecision = decision
        end
    end
    
    if bestDecision then HSExecute(bestDecision.id, snapshot) end
    
    if snapshot.inMelee and snapshot.targetExists then
        if hsCaches.attackSlot > 0 then
            if not IsCurrentAction(hsCaches.attackSlot) then 
                AttackTarget() 
                HSDebug("EXEC", "Auto-Attack Started")
            end
        else
            if (GetTime() - (hsState.lastAttackCmd or 0)) > 2.5 then
                AttackTarget()
                hsState.lastAttackCmd = GetTime()
                HSDebug("EXEC", "Auto-Attack Command Issued")
            end
        end
    end
end

-- ============================================================
-- DRAGGABLE HUD
-- ============================================================
local HolyCatHUD = CreateFrame("Frame", "HolyCatHUDFrame", UIParent)
HolyCatHUD:SetWidth(150) HolyCatHUD:SetHeight(100) HolyCatHUD:SetPoint("CENTER", 200, -150)
HolyCatHUD:SetBackdrop({bgFile = "Interface\\Tooltips\\UI-Tooltip-Background", edgeFile = "Interface\\Tooltips\\UI-Tooltip-Border", tile = true, tileSize = 16, edgeSize = 16, insets = { left = 4, right = 4, top = 4, bottom = 4 }})
HolyCatHUD:SetBackdropColor(0, 0, 0, 0.8) HolyCatHUD:SetMovable(true) HolyCatHUD:EnableMouse(true) HolyCatHUD:RegisterForDrag("LeftButton")
HolyCatHUD:SetScript("OnDragStart", function() this:StartMoving() end) HolyCatHUD:SetScript("OnDragStop", function() this:StopMovingOrSizing() end)

HolyCatHUD.title = HolyCatHUD:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
HolyCatHUD.title:SetPoint("TOPLEFT", 10, -10) HolyCatHUD.title:SetText("|cffd08524HolyCat|r")
HolyCatHUD.shiftText = HolyCatHUD:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
HolyCatHUD.shiftText:SetPoint("TOPLEFT", 10, -30)
HolyCatHUD.rakeText = HolyCatHUD:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
HolyCatHUD.rakeText:SetPoint("TOPLEFT", 10, -45)
HolyCatHUD.mcpText = HolyCatHUD:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
HolyCatHUD.mcpText:SetPoint("TOPLEFT", 10, -60)
HolyCatHUD.distText = HolyCatHUD:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
HolyCatHUD.distText:SetPoint("TOPLEFT", 10, -75)

local lastHUDUpdate = 0
HolyCatHUD:SetScript("OnUpdate", function()
    if GetTime() - lastHUDUpdate < 0.2 then return end
    lastHUDUpdate = GetTime()
    HolyCatHUD.shiftText:SetText("P.Shift: " .. (hsConfig.usePowershift and "|cff24D040ON|r" or "|cffD02424OFF|r"))

    if hsState.rakeActive then
        if hsState.rakeExpiration > 0 then
            local remain = hsState.rakeExpiration - GetTime()
            if remain > 0 then
                HolyCatHUD.rakeText:SetText(string.format("Rake: |cffEEDD22%.1fs|r", remain))
            else
                HolyCatHUD.rakeText:SetText("Rake: |cffD02424MISSING|r")
            end
        else
            HolyCatHUD.rakeText:SetText("Rake: |cffEEDD22UP|r")
        end
    else
        HolyCatHUD.rakeText:SetText("Rake: |cffD02424MISSING|r")
    end
    
    HolyCatHUD.mcpText:SetText("MCP: " .. (hsState.mcpReady and "|cff24D040READY|r" or "|cffAAAAAACooldown|r"))
    
    if has_unitxp and hsState.targetExists and not hsState.targetDead then
        local distStr = ""
        if hsState.currentDistance then
            local color = hsState.currentDistance <= 5.0 and "|cff24D040" or "|cffD02424"
            distStr = string.format("%s%.1fyd|r", color, hsState.currentDistance)
        else
            distStr = "|cffAAAAAA---|r"
        end
        local losStr = hsState.currentLoS and "|cff24D040LoS|r" or "|cffD02424Wall|r"
        HolyCatHUD.distText:SetText("Pos: " .. distStr .. " (" .. losStr .. ")")
    else
        HolyCatHUD.distText:SetText("")
    end
end)

-- ============================================================
-- COMMANDS & FRAME INIT
-- ============================================================

local function HolyCat_SlashCommand(msg)
    local _, _, cmd, arg = string.find(msg or "", "^(%S*)%s*(.-)$")
    cmd = string.lower(cmd or "")
    
    if cmd == "" or cmd == "dps" then HolyCat_CommandDPS()
    elseif cmd == "shift" then hsConfig.usePowershift = ParseToggle(hsConfig.usePowershift, arg); HSPrint("Powershift: " .. (hsConfig.usePowershift and "|cff24D040ON|r" or "|cffD02424OFF|r"))
    elseif cmd == "berserk" then hsConfig.useBerserk = ParseToggle(hsConfig.useBerserk, arg); HSPrint("Berserk: " .. (hsConfig.useBerserk and "|cff24D040ON|r" or "|cffD02424OFF|r"))
    elseif cmd == "tiger" then hsConfig.useTigerFury = ParseToggle(hsConfig.useTigerFury, arg); HSPrint("Tiger's Fury: " .. (hsConfig.useTigerFury and "|cff24D040ON|r" or "|cffD02424OFF|r"))
    elseif cmd == "cower" then hsConfig.useCower = ParseToggle(hsConfig.useCower, arg); HSPrint("Smart Cower: " .. (hsConfig.useCower and "|cff24D040ON|r" or "|cffD02424OFF|r"))
    elseif cmd == "ff" then hsConfig.useFF = ParseToggle(hsConfig.useFF, arg); HSPrint("Faerie Fire: " .. (hsConfig.useFF and "|cff24D040ON|r" or "|cffD02424OFF|r"))
    elseif cmd == "hud" then hsConfig.showHUD = ParseToggle(hsConfig.showHUD, arg); if hsConfig.showHUD then HolyCatHUD:Show() else HolyCatHUD:Hide() end; HSPrint("HUD: " .. (hsConfig.showHUD and "|cff24D040ON|r" or "|cffD02424OFF|r"))
    elseif cmd == "items" then hsConfig.useItems = ParseToggle(hsConfig.useItems, arg); HSPrint("Auto-Items/Runes: " .. (hsConfig.useItems and "|cff24D040ON|r" or "|cffD02424OFF|r"))
    elseif cmd == "mcp" then hsConfig.useMCP = ParseToggle(hsConfig.useMCP, arg); HSPrint("Auto-MCP (Bosses): " .. (hsConfig.useMCP and "|cff24D040ON|r" or "|cffD02424OFF|r"))
    elseif cmd == "trinkets" then hsConfig.useTrinkets = ParseToggle(hsConfig.useTrinkets, arg); HSPrint("Auto-Trinkets: " .. (hsConfig.useTrinkets and "|cff24D040ON|r" or "|cffD02424OFF|r"))
    elseif cmd == "opener" then hsConfig.useOpener = ParseToggle(hsConfig.useOpener, arg); HSPrint("Stealth Opener: " .. (hsConfig.useOpener and "|cff24D040ON|r" or "|cffD02424OFF|r"))
    elseif cmd == "anticc" then hsConfig.useAntiCC = ParseToggle(hsConfig.useAntiCC, arg); HSPrint("Anti-CC Reshift: " .. (hsConfig.useAntiCC and "|cff24D040ON|r" or "|cffD02424OFF|r"))
    elseif cmd == "motw" then hsConfig.useMotw = ParseToggle(hsConfig.useMotw, arg); HSPrint("Auto-MotW: " .. (hsConfig.useMotw and "|cff24D040ON|r" or "|cffD02424OFF|r"))
    elseif cmd == "status" then
        if hsCaches.buffs.dirty then HSRebuildBuffCache() end
        HSPrint("--- HolyCat v" .. HS.VERSION .. " Status ---")
        HSPrint("Powershift:   " .. (hsConfig.usePowershift and "|cff24D040ON|r" or "|cffD02424OFF|r"))
        HSPrint("Smart Cower:  " .. (hsConfig.useCower and "|cff24D040ON|r" or "|cffD02424OFF|r"))
        HSPrint("Auto-Trinkets:" .. (hsConfig.useTrinkets and "|cff24D040ON|r" or "|cffD02424OFF|r"))
        HSPrint("Faerie Fire:  " .. (hsConfig.useFF and "|cff24D040ON|r" or "|cffD02424OFF|r"))
        HSPrint("Tiger's Fury: " .. (hsConfig.useTigerFury and "|cff24D040ON|r" or "|cffD02424OFF|r"))
        HSPrint("Berserk:      " .. (hsConfig.useBerserk and "|cff24D040ON|r" or "|cffD02424OFF|r"))
        HSPrint("Auto-MCP:     " .. (hsConfig.useMCP and "|cff24D040ON|r" or "|cffD02424OFF|r"))
        HSPrint("Auto-Items:   " .. (hsConfig.useItems and "|cff24D040ON|r" or "|cffD02424OFF|r"))
        HSPrint("HUD:          " .. (hsConfig.showHUD and "|cff24D040ON|r" or "|cffD02424OFF|r"))
        HSPrint("Stealth Open: " .. (hsConfig.useOpener and "|cff24D040ON|r" or "|cffD02424OFF|r"))
        HSPrint("Anti-CC:      " .. (hsConfig.useAntiCC and "|cff24D040ON|r" or "|cffD02424OFF|r"))
        HSPrint("Auto-MotW:    " .. (hsConfig.useMotw and "|cff24D040ON|r" or "|cffD02424OFF|r"))
        HSPrint("Debug Mode:   " .. (hsConfig.debug and "|cff24D040ON|r" or "|cffD02424OFF|r"))
        HSPrint("DLL Fast-Cast:" .. (has_nampower and "|cff24D040ACTIVE|r" or "|cffD02424MISSING|r"))
        HSPrint("DLL 5yd Check:" .. (has_unitxp and "|cff24D040ACTIVE|r" or "|cffD02424MISSING|r"))
        HSPrint("Cat Form Buff Idx: " .. (hsState.catIdx >= 0 and ("|cff24D040" .. hsState.catIdx .. "|r") or "|cffD02424NOT FOUND|r"))
    
    elseif cmd == "debug" then 
        if string.find(arg, "^show") then
            local _, _, lines = string.find(arg, "^show%s+(%d+)")
            local n = tonumber(lines) or 50
            HolyCat_SlashCommand("log " .. n)
        else
            hsConfig.debug = ParseToggle(hsConfig.debug, arg)
            HSPrint("Debug Mode: " .. (hsConfig.debug and "|cff24D040ON|r" or "|cffD02424OFF|r"))
        end
        
    elseif cmd == "log" then
        local n = tonumber(arg) or 20
        if n > hsDebugCount then n = hsDebugCount end
        
        HSPrint("--- HolyCat Debug Log (Last " .. n .. " lines) ---")
        if hsDebugCount == 0 then
            HSPrint("Log is empty. (Make sure /hc debug is ON and you have been in combat).")
        else
            local startIdx = hsDebugHead - n
            if startIdx < 1 then 
                startIdx = startIdx + HS.DEBUG_MAX_LINES 
            end

            local currIdx = startIdx
            for i = 1, n do
                HSPrint(HSDebugLog[currIdx])
                currIdx = currIdx + 1
                if currIdx > HS.DEBUG_MAX_LINES then currIdx = 1 end
            end
        end
    else
        HSPrint("Commands: /hc dps, /hc shift, /hc tiger, /hc ff, /hc berserk, /hc hud, /hc items, /hc mcp, /hc trinkets, /hc cower, /hc opener, /hc anticc, /hc motw, /hc status, /hc debug[on/off], /hc log[lines]")
    end
end

local HolyCatFrame = CreateFrame("Frame", nil)
HolyCatFrame:SetScript("OnEvent", function()
    local event, arg1 = event, arg1
    
    if event == "VARIABLES_LOADED" then
        if _G.HCConfig then
            for k, v in pairs(_G.HCConfig) do
                if hsConfig[k] ~= nil then hsConfig[k] = v end
            end
        end
        _G.HCConfig = hsConfig
        
        if hsConfig.hudPos then
            HolyCatHUD:ClearAllPoints()
            HolyCatHUD:SetPoint(hsConfig.hudPos.point, UIParent, hsConfig.hudPos.relativePoint, hsConfig.hudPos.x, hsConfig.hudPos.y)
        end
        
        HSLoadTalents() 
        HSBuildActionCache()
        if hsConfig.showHUD then HolyCatHUD:Show() else HolyCatHUD:Hide() end
        HSPrint("v" .. HS.VERSION .. " loaded! Type '/hc status' to check DLL connections.")
        
    elseif event == "PLAYER_LOGOUT" then
        local point, _, relativePoint, xOfs, yOfs = HolyCatHUD:GetPoint()
        hsConfig.hudPos = { point = point, relativePoint = relativePoint, x = xOfs, y = yOfs }
        _G.HCConfig = hsConfig
        
    elseif event == "PLAYER_ENTERING_WORLD" then 
        HSRebuildSpellCache()
        HSBuildActionCache() 
        HSLoadTalents() 
        HSCacheShapeshift()
        HSUpdateMCPState()
        HSRebuildItemCache()
        hsCaches.buffs.dirty = true -- Deferred initialization safety
        
    elseif event == "LEARNED_SPELL_IN_TAB" then HSRebuildSpellCache()
    elseif event == "UPDATE_SHAPESHIFT_FORMS" then HSCacheShapeshift()
    elseif event == "BAG_UPDATE" then HSRebuildItemCache()
    elseif event == "ACTIONBAR_SLOT_CHANGED" then HSBuildActionCache()
    elseif event == "UNIT_INVENTORY_CHANGED" and arg1 == "player" then HSUpdateMCPState()
    elseif event == "CHARACTER_POINTS_CHANGED" then HSLoadTalents() HSRebuildSpellCache()
    elseif event == "PLAYER_REGEN_DISABLED" then 
        hsState.combatStartTime = GetTime() 
        hsState.combatEndTime = 0
        hsState.positionalLockout = 0 
        hsState.losLockout = 0
    elseif event == "PLAYER_REGEN_ENABLED" then
        hsState.combatStartTime = 0
        hsState.combatEndTime = GetTime()
        hsState.lastExecution["Finisher"] = nil
        hsState.positionalLockout = 0
        hsState.losLockout = 0
        hsState.rakeActive = false
        hsState.rakeExpiration = 0
        hsState.rakeLocalExpiration = 0
        hsState.ripLocalExpiration = 0
        hsState.targetRipExpiration = 0
        hsState.targetBleedCount = 0
        hsState.targetHasFaerieFire = false
    elseif event == "PLAYER_TARGET_CHANGED" then
        HSUpdatePositionState(event, arg1)
        hsCaches.buffs.dirty = true
        hsState.rakeActive = false
        hsState.rakeExpiration = 0
        hsState.targetRipExpiration = 0
        hsState.targetBleedCount = 0
        hsState.targetHasFaerieFire = false
        hsState.lastTargetDebuffScan = 0  -- force immediate rescan on new target
        -- Invalidate distance cache so first snapshot gets a fresh reading
        hsState.lastDistanceUpdate = 0
        hsState.lastLoSCheck = 0
        hsState.cachedDistance = nil
    elseif event == "UNIT_HEALTH" and arg1 == "target" then 
        hsState.targetDead = UnitIsDead("target") and true or false
        if hsState.targetDead then
            hsState.rakeActive = false
            hsState.rakeExpiration = 0
            hsState.rakeLocalExpiration = 0
            hsState.ripLocalExpiration = 0
        end
    elseif event == "CHAT_MSG_SPELL_SELF_DAMAGE" or event == "UI_ERROR_MESSAGE" then 
        HSUpdatePositionState(event, arg1)
    elseif event == "PLAYER_AURAS_CHANGED" then 
        hsCaches.buffs.dirty = true 
    end
end)

HolyCatFrame:RegisterEvent("PLAYER_ENTERING_WORLD")
HolyCatFrame:RegisterEvent("VARIABLES_LOADED")
HolyCatFrame:RegisterEvent("PLAYER_LOGOUT")
HolyCatFrame:RegisterEvent("PLAYER_REGEN_ENABLED")
HolyCatFrame:RegisterEvent("PLAYER_REGEN_DISABLED")
HolyCatFrame:RegisterEvent("PLAYER_TARGET_CHANGED")
HolyCatFrame:RegisterEvent("UNIT_HEALTH")
HolyCatFrame:RegisterEvent("CHAT_MSG_SPELL_SELF_DAMAGE")
HolyCatFrame:RegisterEvent("UI_ERROR_MESSAGE")
HolyCatFrame:RegisterEvent("ACTIONBAR_SLOT_CHANGED")
HolyCatFrame:RegisterEvent("LEARNED_SPELL_IN_TAB")
HolyCatFrame:RegisterEvent("UPDATE_SHAPESHIFT_FORMS")
HolyCatFrame:RegisterEvent("CHARACTER_POINTS_CHANGED")
HolyCatFrame:RegisterEvent("PLAYER_AURAS_CHANGED")
HolyCatFrame:RegisterEvent("UNIT_INVENTORY_CHANGED")
HolyCatFrame:RegisterEvent("BAG_UPDATE")

SlashCmdList["HOLYCAT"] = HolyCat_SlashCommand
SLASH_HOLYCAT1 = "/hc"