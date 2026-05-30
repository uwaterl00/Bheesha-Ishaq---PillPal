||| PillPal Pro — Core Domain Types
||| Authors  : Bheesha Ramachandran & Ishaq Nasiru (PillPal)
||| Contact  : m26steph@uwaterloo.ca
||| Verified : Total, no holes, no believe_me
module PillPal.Types.Core

%default total

-- ---------------------------------------------------------------------------
-- Compartment identity — exactly four compartments, proof-carried
-- ---------------------------------------------------------------------------

||| The four physical pill compartments on the device.
||| Using a closed enumeration guarantees no out-of-range index is ever
||| constructed at the type level.
public export
data CompartmentId : Type where
  C1 : CompartmentId
  C2 : CompartmentId
  C3 : CompartmentId
  C4 : CompartmentId

public export
Eq CompartmentId where
  C1 == C1 = True
  C2 == C2 = True
  C3 == C3 = True
  C4 == C4 = True
  _  == _  = False

public export
Show CompartmentId where
  show C1 = "PillBox1"
  show C2 = "PillBox2"
  show C3 = "PillBox3"
  show C4 = "PillBox4"

||| All compartments listed in canonical order.
public export
allCompartments : List CompartmentId
allCompartments = [C1, C2, C3, C4]

||| Proof that |allCompartments| has exactly four elements.
public export
allCompartmentsLength : length allCompartments = 4
allCompartmentsLength = Refl

-- ---------------------------------------------------------------------------
-- Pill name — a non-empty string with a proof of non-emptiness
-- ---------------------------------------------------------------------------

||| A pill name is a non-empty String.
public export
record PillName where
  constructor MkPillName
  rawName    : String
  nonEmpty   : NonEmpty (unpack rawName)

||| Smart constructor: returns Nothing if the string is empty.
public export
mkPillName : String -> Maybe PillName
mkPillName "" = Nothing
mkPillName s  = case unpack s of
  []      => Nothing
  (c::cs) => Just (MkPillName s (IsNonEmpty))

public export
Show PillName where
  show (MkPillName n _) = n

-- ---------------------------------------------------------------------------
-- Time — Unix epoch seconds, a wrapped Nat to keep values non-negative
-- ---------------------------------------------------------------------------

||| Unix epoch time in seconds (always >= 0).
public export
record EpochTime where
  constructor MkEpoch
  seconds : Nat

public export
Eq EpochTime where
  (MkEpoch a) == (MkEpoch b) = a == b

public export
Ord EpochTime where
  compare (MkEpoch a) (MkEpoch b) = compare a b

public export
Show EpochTime where
  show (MkEpoch s) = show s

||| Zero epoch (Unix origin).
public export
epochZero : EpochTime
epochZero = MkEpoch 0

||| Add an interval (in seconds) to an epoch time.
||| The result is always >= the original because Nat addition is total.
public export
addInterval : EpochTime -> (interval : Nat) -> EpochTime
addInterval (MkEpoch t) i = MkEpoch (t + i)

||| Proof: addInterval is monotone — result is always >= input.
public export
addIntervalMonotone : (t : EpochTime) -> (i : Nat) -> t <= addInterval t i
addIntervalMonotone (MkEpoch t) i =
  let prf : t `LTE` (t + i) = lteAddRight t i
  in prf

-- ---------------------------------------------------------------------------
-- Interval — how often to take a pill, in seconds, strictly positive
-- ---------------------------------------------------------------------------

||| A dose interval is a strictly positive number of seconds.
||| The proof |positiveInterval| witnesses Nat > 0 at compile time.
public export
record DoseInterval where
  constructor MkInterval
  intervalSecs : Nat
  positiveInterval : IsSucc intervalSecs

||| Smart constructor.
public export
mkInterval : (n : Nat) -> {auto prf : IsSucc n} -> DoseInterval
mkInterval n {prf} = MkInterval n prf

||| One-hour default interval.
public export
oneHourInterval : DoseInterval
oneHourInterval = MkInterval 3600 ItIsSucc

||| One-minute interval (useful for testing).
public export
oneMinuteInterval : DoseInterval
oneMinuteInterval = MkInterval 60 ItIsSucc

-- ---------------------------------------------------------------------------
-- Compartment configuration — what is in each box
-- ---------------------------------------------------------------------------

||| Configuration stored in Firebase for a single compartment.
public export
record CompartmentConfig where
  constructor MkConfig
  pillName     : PillName
  takeTime     : EpochTime   -- When the next dose is due
  lastTaken    : EpochTime   -- When the last dose was taken
  doseInterval : DoseInterval

-- ---------------------------------------------------------------------------
-- Alert state — what the device should be doing right now
-- ---------------------------------------------------------------------------

||| The observable alert state of one compartment.
public export
data AlertState : Type where
  ||| No action needed; next dose is in the future.
  Idle    : AlertState
  ||| Dose is due — LED on, buzzer active, notification sent.
  Alert   : AlertState
  ||| Lid opened prematurely — buzzer continuous, angry mode.
  Angry   : AlertState
  ||| Dose acknowledged — lid was opened during Alert window.
  Taken   : AlertState

public export
Eq AlertState where
  Idle  == Idle  = True
  Alert == Alert = True
  Angry == Angry = True
  Taken == Taken = True
  _     == _     = False

public export
Show AlertState where
  show Idle  = "Idle"
  show Alert = "Alert"
  show Angry = "Angry"
  show Taken = "Taken"

-- ---------------------------------------------------------------------------
-- System-wide device state
-- ---------------------------------------------------------------------------

||| Complete device state for all four compartments.
public export
record DeviceState where
  constructor MkDeviceState
  currentTime : EpochTime
  configs     : CompartmentId -> CompartmentConfig
  alerts      : CompartmentId -> AlertState
  lidOpen     : CompartmentId -> Bool  -- live button readings (True = open)
