||| PillPal Pro — Firebase Wire Types
||| Authors  : Bheesha & Ishaq Nasiru (PillPal)
||| Contact  : m26steph@uwaterloo.ca
||| Verified : Total, no holes, no believe_me
module PillPal.Types.Firebase

import PillPal.Types.Core

%default total

-- ---------------------------------------------------------------------------
-- Firebase JSON schema (exactly mirrors the existing database structure)
-- ---------------------------------------------------------------------------

||| Raw JSON record for a single pill box, as stored in Firebase.
||| Field names match the existing production schema exactly.
public export
record FirebasePillBox where
  constructor MkFirebasePillBox
  name             : String  -- pill name (may be empty in DB, we validate on read)
  takeTime         : Integer -- Unix epoch seconds for next dose
  takeTimeInterval : Integer -- Interval in seconds between doses
  time             : Integer -- When the last dose was taken (Unix epoch)

||| Full database root: four pill boxes keyed by their canonical names.
public export
record FirebaseRoot where
  constructor MkFirebaseRoot
  pillBox1 : FirebasePillBox
  pillBox2 : FirebasePillBox
  pillBox3 : FirebasePillBox
  pillBox4 : FirebasePillBox

-- ---------------------------------------------------------------------------
-- Firebase base URL (the existing production database)
-- ---------------------------------------------------------------------------

public export
firebaseBaseUrl : String
firebaseBaseUrl = "https://vitavault-ddba4-default-rtdb.firebaseio.com"

public export
pillBoxesUrl : String
pillBoxesUrl = firebaseBaseUrl ++ "/PillBoxes.json"

public export
pillBoxUrl : CompartmentId -> String
pillBoxUrl cid = firebaseBaseUrl ++ "/PillBoxes/" ++ show cid ++ ".json"

-- ---------------------------------------------------------------------------
-- Validation: converting raw Firebase types to domain types
-- ---------------------------------------------------------------------------

||| Errors that can arise when validating a Firebase record.
public export
data FirebaseError : Type where
  ||| The pill name field was empty.
  EmptyPillName   : FirebaseError
  ||| The takeTime field was negative (invalid epoch).
  NegativeTakeTime : Integer -> FirebaseError
  ||| The interval was zero or negative.
  NonPositiveInterval : Integer -> FirebaseError

public export
Show FirebaseError where
  show EmptyPillName           = "Empty pill name in Firebase record"
  show (NegativeTakeTime t)    = "Negative takeTime: " ++ show t
  show (NonPositiveInterval i) = "Non-positive interval: " ++ show i

||| Convert a raw Integer epoch to a validated EpochTime.
||| Returns Left with a proof-carrying error if the value is negative.
public export
validateEpoch : Integer -> Either FirebaseError EpochTime
validateEpoch i =
  case i >= 0 of
    True  => Right (MkEpoch (cast i))
    False => Left  (NegativeTakeTime i)

||| Convert a raw Integer interval to a validated DoseInterval.
public export
validateInterval : Integer -> Either FirebaseError DoseInterval
validateInterval i =
  case i > 0 of
    True  =>
      let n : Nat = cast i
      in case n of
        Z     => Left (NonPositiveInterval i)  -- cast edge case
        (S k) => Right (MkInterval (S k) ItIsSucc)
    False => Left (NonPositiveInterval i)

||| Fully validate a raw FirebasePillBox into a domain CompartmentConfig.
||| All validation errors are reported explicitly; nothing is silently coerced.
public export
validatePillBox : FirebasePillBox -> Either FirebaseError CompartmentConfig
validatePillBox fb = do
  name     <- case mkPillName fb.name of
                Nothing => Left EmptyPillName
                Just n  => Right n
  takeT    <- validateEpoch fb.takeTime
  lastT    <- validateEpoch fb.time
  interval <- validateInterval fb.takeTimeInterval
  pure (MkConfig name takeT lastT interval)

-- ---------------------------------------------------------------------------
-- Firebase PATCH payload — what we send back when a dose is taken
-- ---------------------------------------------------------------------------

||| Payload sent to Firebase when a compartment lid is opened (dose taken).
public export
record TakenPayload where
  constructor MkTakenPayload
  takenAtTime  : EpochTime  -- When the lid was opened
  nextTakeTime : EpochTime  -- When the next dose is due

||| Proof: the nextTakeTime is always after takenAtTime.
public export
takenPayloadSane :
    (t : EpochTime) ->
    (interval : DoseInterval) ->
    let payload = MkTakenPayload t (addInterval t interval.intervalSecs)
    in payload.takenAtTime < payload.nextTakeTime
takenPayloadSane (MkEpoch t) (MkInterval i prf) =
  ltAddSuccRight t i prf

||| Serialise a TakenPayload into a Firebase PATCH JSON string.
public export
serialiseTakenPayload : TakenPayload -> String
serialiseTakenPayload (MkTakenPayload (MkEpoch taken) (MkEpoch next)) =
  "{\"time\":" ++ show taken ++ ", \"takeTime\":" ++ show next ++ "}"
