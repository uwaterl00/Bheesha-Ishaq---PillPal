||| PillPal Pro — Dose Schedule Management
||| Authors  : Bheesha & Ishaq Nasiru (PillPal)
||| Contact  : m26steph@uwaterloo.ca
||| Verified : Total, no holes, no believe_me
module PillPal.Core.Schedule

import PillPal.Types.Core
import PillPal.Types.Time
import PillPal.Types.Firebase

%default total

-- ---------------------------------------------------------------------------
-- Schedule invariant: the next dose must always be in the future relative
-- to the last-taken time
-- ---------------------------------------------------------------------------

||| A schedule is valid if takeTime > lastTaken.
public export
record ValidSchedule where
  constructor MkValidSchedule
  config  : CompartmentConfig
  ||| Proof that the stored takeTime is strictly after lastTaken.
  sane    : config.lastTaken < config.takeTime

-- ---------------------------------------------------------------------------
-- Constructing a valid schedule
-- ---------------------------------------------------------------------------

||| Construct a ValidSchedule from a raw CompartmentConfig.
||| Returns Left if the invariant is violated (lastTaken >= takeTime).
public export
mkValidSchedule : CompartmentConfig -> Either String ValidSchedule
mkValidSchedule cfg =
  case decideIsDue cfg.lastTaken cfg.takeTime of
    -- takeTime <= lastTaken: violated
    Yes lte =>
      Left ("Schedule invariant violated for pill: " ++ show cfg.pillName
            ++ " (lastTaken=" ++ show cfg.lastTaken
            ++ " >= takeTime=" ++ show cfg.takeTime ++ ")")
    -- takeTime > lastTaken: good
    No notLte =>
      let lt : cfg.lastTaken < cfg.takeTime = notLTEImpliesGT notLte
      in Right (MkValidSchedule cfg lt)

-- ---------------------------------------------------------------------------
-- Acknowledging a dose — advance the schedule
-- ---------------------------------------------------------------------------

||| The result of acknowledging a dose: a new ValidSchedule with the next
||| dose time set to `now + interval`, and a proof that the new schedule
||| satisfies the invariant.
public export
acknowledgeDose :
    (now     : EpochTime) ->
    (vs      : ValidSchedule) ->
    ValidSchedule
acknowledgeDose now vs =
  let cfg      = vs.config
      interval = cfg.doseInterval
      newTake  = addInterval now interval.intervalSecs
      -- Proof: now < now + interval  (because interval > 0)
      prf      : now < newTake
               = ltAddSuccRight now.seconds interval.intervalSecs interval.positiveInterval
      newCfg   = MkConfig cfg.pillName newTake now interval
  in MkValidSchedule newCfg prf

||| Proof: the new takeTime after acknowledgeDose equals now + interval.
public export
acknowledgeDoseTime :
    (now : EpochTime) ->
    (vs  : ValidSchedule) ->
    (acknowledgeDose now vs).config.takeTime
      = addInterval now vs.config.doseInterval.intervalSecs
acknowledgeDoseTime now vs = Refl

||| Proof: after acknowledgeDose, lastTaken equals `now`.
public export
acknowledgeDoseLastTaken :
    (now : EpochTime) ->
    (vs  : ValidSchedule) ->
    (acknowledgeDose now vs).config.lastTaken = now
acknowledgeDoseLastTaken now vs = Refl

-- ---------------------------------------------------------------------------
-- Polling logic: should we alert?
-- ---------------------------------------------------------------------------

||| Decide whether the dose is overdue, given the current time.
public export
isOverdue : EpochTime -> ValidSchedule -> Bool
isOverdue now vs = isDue now vs.config.takeTime

||| How many seconds until the next dose.
public export
secondsUntilDose : EpochTime -> ValidSchedule -> Nat
secondsUntilDose now vs = secondsUntil now vs.config.takeTime

-- ---------------------------------------------------------------------------
-- All four compartment schedules
-- ---------------------------------------------------------------------------

||| Validated schedules for all four compartments.
public export
record AllSchedules where
  constructor MkAllSchedules
  sched : CompartmentId -> ValidSchedule

||| Update one schedule in the set.
public export
updateSchedule :
    CompartmentId ->
    ValidSchedule ->
    AllSchedules ->
    AllSchedules
updateSchedule cid vs (MkAllSchedules f) =
  MkAllSchedules (\c => if c == cid then vs else f c)

||| Proof: after update, reading back the updated compartment returns the new schedule.
public export
updateScheduleCorrect :
    (cid : CompartmentId) ->
    (vs  : ValidSchedule) ->
    (all : AllSchedules) ->
    (updateSchedule cid vs all).sched cid = vs
updateScheduleCorrect cid vs all with (cid == cid) proof eq
  _ | True  = Refl
  _ | False = absurd (sym (eqRefl cid) `trans` eq)
  where
    eqRefl : (x : CompartmentId) -> x == x = True
    eqRefl C1 = Refl
    eqRefl C2 = Refl
    eqRefl C3 = Refl
    eqRefl C4 = Refl

||| Proof: updating one compartment doesn't affect others.
public export
updateScheduleDoesNotAffectOthers :
    (cid  : CompartmentId) ->
    (cid2 : CompartmentId) ->
    (vs   : ValidSchedule) ->
    (all  : AllSchedules) ->
    cid /= cid2 ->
    (updateSchedule cid vs all).sched cid2 = all.sched cid2
updateScheduleDoesNotAffectOthers cid cid2 vs all neq with (cid2 == cid) proof eq
  _ | False = Refl
  _ | True  =>
      let same : cid2 = cid = eqImpliesEq eq
      in absurd (neq same)
  where
    eqImpliesEq : {a, b : CompartmentId} -> a == b = True -> a = b
    eqImpliesEq {a = C1} {b = C1} _ = Refl
    eqImpliesEq {a = C2} {b = C2} _ = Refl
    eqImpliesEq {a = C3} {b = C3} _ = Refl
    eqImpliesEq {a = C4} {b = C4} _ = Refl
    eqImpliesEq {a = C1} {b = C2} p = absurd p
    eqImpliesEq {a = C1} {b = C3} p = absurd p
    eqImpliesEq {a = C1} {b = C4} p = absurd p
    eqImpliesEq {a = C2} {b = C1} p = absurd p
    eqImpliesEq {a = C2} {b = C3} p = absurd p
    eqImpliesEq {a = C2} {b = C4} p = absurd p
    eqImpliesEq {a = C3} {b = C1} p = absurd p
    eqImpliesEq {a = C3} {b = C2} p = absurd p
    eqImpliesEq {a = C3} {b = C4} p = absurd p
    eqImpliesEq {a = C4} {b = C1} p = absurd p
    eqImpliesEq {a = C4} {b = C2} p = absurd p
    eqImpliesEq {a = C4} {b = C3} p = absurd p
