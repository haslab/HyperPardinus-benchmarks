
open util/boolean
sig OpId {}

abstract sig Op {}
abstract sig Push, Pop extends Op {}
one sig PushRight, PushLeft extends Push {}
one sig PopRight, PopLeft extends Pop {}
sig Val {}
one sig Claimed extends Val {}

// struct Node {valtype V; Node *L; Node *R}
sig Node {}
one sig Dummy extends Node {}
