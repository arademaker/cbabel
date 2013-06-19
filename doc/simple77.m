fmod SIMPLE is
  pr NAT .
  inc MODEL-CHECKER .

**** Model checker sorts and ops states, transitions, results
***  sorts State RuleName Transition TransitionList ModelCheckResult .
***  subsort Qid < RuleName .
***  ops unlabeled deadlock : -> RuleName .
***  op {_,_} : State RuleName -> Transition .
***  subsort Transition < TransitionList .
***  op nil : -> TransitionList [ctor] .
***  op __ : TransitionList TransitionList -> TransitionList
***                  [ctor assoc id: nil] .
***  subsort Bool < ModelCheckResult .
***  op counterexample : TransitionList TransitionList -> ModelCheckResult 
***                            [ctor] .
***  op _|=_ : State Formula -> [ModelCheckResult]

*** avoid mc search for testing propositions

  op _sat_ : State Prop -> ModelCheckResult .
  eq (S:State |= P:Prop) = (S:State sat P:Prop) .

  sort RuleNameList .
  subsort RuleName < RuleNameList .
  op nil : -> RuleNameList .
  op __ : RuleNameList RuleNameList -> RuleNameList [assoc id: nil] .

  sort StateList .
  subsort State < StateList .
  op nil : -> StateList .
  op __ : StateList StateList -> StateList [assoc id: nil] .

  ops getPre getPost : ModelCheckResult -> TransitionList .
  eq getPre(b:Bool) = nil .
  eq getPost(b:Bool) = nil .
  eq getPre(counterexample(tl0:TransitionList,tl1:TransitionList))
        = tl0:TransitionList .
  eq getPost(counterexample(tl0:TransitionList,tl1:TransitionList))
        = tl1:TransitionList .

  op getState  : Transition -> State .
  op getRuleName : Transition -> RuleName .
  eq getState({s:State,rn:RuleName}) = s:State .
  eq getRuleName({s:State,rn:RuleName}) = rn:RuleName .

  op getRuleNames : TransitionList -> RuleNameList .
  eq getRuleNames(nil) = nil .
  eq getRuleNames({s:State,rn:RuleName} tl:TransitionList) = 
      rn:RuleName getRuleNames(tl:TransitionList) .

  op length : TransitionList -> Nat .
  eq length(nil) = 0 .
  eq length(tr:Transition tl:TransitionList) = length(tl:TransitionList) + 1 .

  sort SimplePath .
  op spath : RuleNameList State -> SimplePath .
  op noPath : -> SimplePath .
  op getState : SimplePath -> State .
  eq getState(spath(rls:RuleNameList,s:State)) = s:State .

*** assumes that modelcheck result is a boolean or that the 
*** concatenation of the transition lists contains a state that satisfies 
*** the proposition 

  op getPath : Prop ModelCheckResult -> SimplePath .
  op getPathx : Prop RuleNameList TransitionList -> SimplePath .

  eq getPath(P:Prop, b:Bool) = noPath .
  eq getPath(P:Prop, counterexample(tl0:TransitionList,tl1:TransitionList)) 
      = getPathx(P:Prop, nil, (tl0:TransitionList tl1:TransitionList) ) .

  eq getPathx(P:Prop, rnl:RuleNameList, nil) = noPath .
  eq getPathx(P:Prop, 
              rnl:RuleNameList, 
              {s:State, rn:RuleName} tl:TransitionList)
    
    = if ((s:State sat P:Prop) :: Bool)  *** ((s:State |= P:Prop) :: Bool)
      then spath(rnl:RuleNameList, s:State)
      else  getPathx(P:Prop, (rnl:RuleNameList rn:RuleName), tl:TransitionList)
      fi .

  op findPath : State Prop -> SimplePath .
  eq findPath(S:State, P:Prop) =  getPath(P:Prop, S:State |= ~ <> P:Prop) .

  sort FullPath .
  op fpath : StateList RuleNameList State -> FullPath .
  op noPath : -> FullPath .
  op getState : FullPath -> State .
  eq getState(fpath(stl:StateList, rls:RuleNameList,s:State)) = s:State .
  op getRuleNames : FullPath -> RuleNameList .
  eq getRuleNames(fpath(stl:StateList, rls:RuleNameList,s:State)) 
        = rls:RuleNameList .


*** assumes further that all rule names preceding the witness state
*** name real rules (are qids in fact).

  op getFPath : Prop ModelCheckResult -> FullPath .
  op getFPathx : Prop StateList RuleNameList TransitionList 
                 -> FullPath .

  eq getFPath(P:Prop, b:Bool) = noPath .
  eq getFPath(P:Prop, counterexample(tl0:TransitionList,tl1:TransitionList)) 
      = getFPathx(P:Prop, nil, nil,
                  (tl0:TransitionList tl1:TransitionList) ) .
*****
  eq getFPathx(P:Prop, stl:StateList, rnl:RuleNameList, nil) = noPath .
  eq getFPathx(P:Prop, stl:StateList, rnl:RuleNameList, 
              {s:State, rn:RuleName} tl:TransitionList)
    = if ((s:State sat P:Prop) :: Bool)  *** ((s:State |= P:Prop) :: Bool)
      then fpath(stl:StateList, rnl:RuleNameList, s:State)
      else  getFPathx(P:Prop, 
                     (stl:StateList s:State), (rnl:RuleNameList rn:RuleName),
                      tl:TransitionList)
      fi .

  op findFPath : State Prop -> FullPath .
  eq findFPath(S:State, P:Prop) =  getFPath(P:Prop, S:State |= ~ <> P:Prop) .

endfm
