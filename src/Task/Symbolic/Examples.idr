module Task.Symbolic.Examples

import Helpers
import Task.Symbolic.Syntax

-- These imports are a convenience for the Repl
import Data.Fuel
import Task.Symbolic.Run

---- Absolute value ------------------------------------------------------------

-- >>> simulate (limit 1) absolute empty
--     [([Insert 0 (Pack (Fresh Int 1))], (Value True &&. (Symbol (Fresh Int 1) >. Value 0), Symbol (Fresh Int 1)))]
absolute : Task None (Symbolic Int)
absolute =
  Edit Unnamed Enter `Step` \x =>
  Branch [ x >. Value 0 ~> Edit Unnamed (View x) ]

---- Selection -----------------------------------------------------------------

-- >>> > simulate (limit 4) selection empty
--     [([Insert 0 (Pack (Fresh Int 2)), Decide 1 "Ok"], (Value True, Symbol (Fresh Int 2))),
--      ([Insert 0 (Pack (Fresh Int 2)), Insert 0 (Pack (Fresh Int 3)), Decide 1 "Ok"], (Value True, Symbol (Fresh Int 3))),
--      ([Insert 0 (Pack (Fresh Int 2)), Insert 0 (Pack (Fresh Int 3)), Insert 0 (Pack (Fresh Int 4)), Decide 1 "Ok"], (Value True, Symbol (Fresh Int 4)))]
selection : Task None (Symbolic Int)
selection =
  Select Unnamed (Edit Unnamed Enter)
    [ "Ok" ~> \x => Edit Unnamed (View x)
    , "Fail" ~> const Fail
    ]

---- Subsidy request -----------------------------------------------------------

Amount : Type
Amount = Symbolic Int

Affirmation : Type
Affirmation = Symbolic Bool

Date : Type
Date = Symbolic Int

-- >>> simulate (limit 4) requestSubsidy empty |> length
--     24
requestSubsidy : Task None Amount
requestSubsidy =
  let
    today : Date
    today = Value 321

    provideDocuments : Task None (Symbolic (Int, Int))
    provideDocuments = Edit Unnamed Enter `Pair` Edit Unnamed Enter

    companyConfirm : Task None Affirmation
    companyConfirm = Pick Unnamed [
      "Confirm" ~> Done (Value True),
      "Deny" ~> Done (Value False)
    ]

    officerApprove : Date -> Date -> Affirmation -> Task None Affirmation
    officerApprove invoiced date confirmed =
      Pick Unnamed [
        "Approve" ~> Test (date -. invoiced <. Value 365 &&. confirmed)
          (Done (Value True))
          (Fail),
        "Reject" ~> Done (Value False)
      ]
  in
  (provideDocuments `Pair` companyConfirm) `Step` \pair =>
  let (inner, confirmed) = ungroup pair in
  let (expenses, invoiced) = ungroup inner in
  officerApprove invoiced today confirmed `Step` \approved =>
  let subsidy = ite approved (min (Value 600) (expenses /. Value 10)) (Value 0) in
  Assert (subsidy >=. Value 0 ==>. confirmed) `Step` \_ =>
  Assert (subsidy >.  Value 0 ==>. approved)  `Step` \_ =>
  Assert (approved ==>. confirmed &&. today -. invoiced <. Value 365) `Step` \_ =>
  Assert (subsidy <=. Value 600) `Step` \_ =>
  Assert (Not approved ==>. subsidy ==. Value 0) `Step` \_ =>
  Edit Unnamed (View subsidy)

---- Computer scientists -------------------------------------------------------

Availability : Type
Availability = Symbolic Bool

Nil : Type
Nil = Symbolic ()

Result : Type
Result = Symbolic Bool

pickup : Ref Triple Availability -> Ref Triple Availability -> Task Triple Nil
pickup this that =
  Edit Unnamed (Watch this) `Step` \thisup =>
  Test thisup (
    Assign (Value False) this `Step` \_ =>
    Edit Unnamed (Watch that) `Continue` \thatup =>
    Test thatup (
      Assign (Value True) this
    ) (
      Fail
    )
  ) (
    Fail
  )

partway : Ref Triple Availability -> Ref Triple Availability -> Task Triple Nil
partway this that =
  Edit Unnamed (Watch that) `Continue` \thatup =>
  Test thatup (
    Assign (Value True) this
  ) (
    Fail
  )

-- >>> simulate (limit 6) computerScientists bools |> length
--     720
scientist : String -> Ref Triple Availability -> Ref Triple Availability -> Task Triple (Symbolic (String, ()))
scientist name left right =
  Edit Unnamed (View (Value name)) `Pair` Pick Unnamed
    [ "Left"  ~> pickup left right
    , "Right" ~> pickup right left
    ]

fork0 : Ref Triple Availability
fork0 = Idx 0
fork1 : Ref Triple Availability
fork1 = Idx 1
fork2 : Ref Triple Availability
fork2 = Idx 2

computerScientists : Task Triple Result
computerScientists =
  (scientist "Alan" fork0 fork1 `Pair` (scientist "Grace" fork1 fork2 `Pair` scientist "Ada" fork2 fork0)) `Step` \_ =>
  Done (Value True)

onlyAlan : Task Triple Result
onlyAlan =
  Assign (Value False) fork1 `Step` \_ =>
  Assign (Value False) fork2 `Step` \_ =>
  (scientist "Alan" fork0 fork1 `Pair` (partway fork1 fork2 `Pair` partway fork2 fork0)) `Step` \_ =>
  Done (Value True)
