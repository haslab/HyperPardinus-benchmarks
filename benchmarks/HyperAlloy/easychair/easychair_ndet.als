enum Decision { Reject, Major, Accept }
sig Reviewer, Article {}

trace sig CMS {
  assigns:       Reviewer some -> some Article,
  var reviews:   Article -> Reviewer -> lone Decision,
  var decisions: Article -> lone Decision
}

// add a new decision to a process
pred review[s:CMS,r:Reviewer,a:Article,d:Decision] {
  a in r.(s.assigns)                   // guard: a is assigned to r
  no r.(a.(s.reviews))                 // guard: r has not yet submitted a review for a
  s.reviews' = s.reviews + a->r->d     // effect: add the review for a
  s.decisions' = s.decisions }         // frame condition: decisions unchanged

fun filter[t:Article] : set Article { t }
fun select[ds: set Decision] : set Decision { ds }

fun criteria[t:Article,s:CMS] : set Decision {
  select[Reviewer.(filter[t].(s.reviews))]
}

// updates a decision in a process given the other reviewers decisions; uses the author oracle
pred decide[s:CMS,a:Article,d:Decision] {
  a not in s.decisions.Decision           // guard: editor has not decided on a
  a.(s.reviews).Decision = s.assigns.a    // guard: all a reviews submitted
  d in criteria[a,s]                      // guard: d is according to specified criteria
  s.decisions' = s.decisions + a->d       // effect: add the decision for a
  s.reviews' = s.reviews }                // frame condition: reviews unchanged

pred stutter[s:CMS] {
  s.reviews' = s.reviews
  s.decisions' = s.decisions
}

pred cms[s:CMS] {
  some Article - Agent.(s.assigns)				   // only scenarios where there are highs

  no s.reviews and no s.decisions                  // initial state

  always some a:Reviewer, t:Article, d:Decision |  // possible events at each state
    review[s,a,t,d] or decide[s,t,d] or stutter[s]

  eventually s.decisions.Decision = Article }      // force eventual decisions

one sig Agent extends Reviewer {}

fun lows[s1,s2:CMS] : set Article {
  Agent.(s1.assigns+s2.assigns)
}

fun highs[s1,s2:CMS] : set Article {
  Article - lows[s1,s2]
}

pred same_assigns[s1,s2:CMS,arts:set Article] {
  s1.assigns :> arts = s2.assigns :> arts
}

pred same_reviews[s1,s2:CMS,arts:set Article] {
  arts <: s1.reviews = arts <: s2.reviews
}

pred same_decisions[s1,s2:CMS,arts:set Article] {
  arts <: s1.decisions = arts <: s2.decisions
}

pred aligned[s1,s2:CMS,arts:set Article] {
  always ((arts <: s1.reviews).Decision = (arts <: s2.reviews).Decision and (arts <: s1.decisions).Decision = (arts <: s2.decisions).Decision)
}

assert NonInterference {
  all s1,s2:CMS | cms[s1] and cms[s2] and aligned[s1,s2,lows[s1,s2]] implies 
    (same_assigns[s1,s2,lows[s1,s2]] and always same_reviews[s1,s2,lows[s1,s2]]) implies always (same_decisions[s1,s2,lows[s1,s2]])
} 


check NonInterference for exactly 2 Reviewer, exactly 2 Article, 10 steps, 0 Int expect 1 
check NonInterference for exactly 3 Reviewer, exactly 2 Article, 10 steps, 0 Int expect 1 

assert GeneralizedNonInterference {
  all s1,s2:CMS | cms[s1] and cms[s2] and aligned[s1,s2,lows[s1,s2]] implies 
      some s3:CMS 
		 { cms[s3]
        same_assigns[s1,s3,lows[s1,s3]] and always same_reviews[s1,s3,lows[s1,s3]]
        always same_decisions[s1,s3,lows[s1,s3]]
        same_assigns[s2,s3,highs[s2,s3]] and always same_reviews[s2,s3,highs[s2,s3]]
      }
}

check GeneralizedNonInterference for exactly 2 Reviewer, exactly 2 Article, 8 steps, 0 Int expect 0 
check GeneralizedNonInterference for exactly 3 Reviewer, exactly 2 Article, 7 steps, 0 Int expect 0 

