
sig Val {}
one sig Claimed extends Val {}
abstract sig Op {}
abstract sig Push, Pop extends Op {}
one sig PushRight, PushLeft extends Push {}
one sig PopRight, PopLeft extends Pop {}

// struct Node {valtype V; Node *L; Node *R}
sig Node {

}
one sig Dummy extends Node {}
