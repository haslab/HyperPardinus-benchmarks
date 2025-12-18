/* 
  ********** Alloy utilities **********
  */
/* 
  Boolean signatures and operations
  */
enum B { T , F }
pred true {
  no (none)
  }
pred false {
  some (none)
  }
/* 
  Integer signatures and operations
  */
abstract sig I {
  }
one sig I0 , I1 , I2 , I3 , I4 , I5 , I6 , I7 extends I {
  }
sig I_0_2 = I0 + I1 + I2 {}
sig I_0_3 = I0 + I1 + I2 + I3 {}
sig I_0_4 = I0 + I1 + I2 + I3 + I4 {}
sig I_1_7 = I1 + I2 + I3 + I4 + I5 + I6 + I7 {}
/* 
  ********** Model starts here **********
  */
/* 
  Model
  */
trace sig Main {
  var line : one I_1_7,
  var receiver_actions : one I_0_2,
  var sender_actions : one I_0_4,
  var take_turns : one I_0_2,
  var thirdparty_actions : one I_0_3 }
/* 
  Initial states
  */
pred init_0[W : Main] {
  ((W . line) in I1) and ((W . thirdparty_actions) in I0) and ((W . receiver_actions) in I0) and ((W . sender_actions) in I0) and ((W . take_turns) in I0)
  }
/* 
  Invariants
  */
pred range_line[W : Main] {
  always ((W . line) in (I1 + I2 + I3 + I4 + I5 + I6 + I7))
  }
pred range_receiver_actions[W : Main] {
  always ((W . receiver_actions) in (I0 + I1 + I2))
  }
pred range_sender_actions[W : Main] {
  always ((W . sender_actions) in (I0 + I1 + I2 + I3 + I4))
  }
pred range_take_turns[W : Main] {
  always ((W . take_turns) in (I0 + I1 + I2))
  }
pred range_thirdparty_actions[W : Main] {
  always ((W . thirdparty_actions) in (I0 + I1 + I2 + I3))
  }
pred invar5[W : Main] {
  always (true)
  }
/* 
  State transitions
  */
pred trans0[W : Main] {
  always (((((W . line) in (I1 + I2 + I4 + I7)) and ((W . take_turns) in (I0 + I1)) and ((W . thirdparty_actions') in I0)) or (((W . line) in I6) and ((W . thirdparty_actions') in I3)) or (((W . line) in (I1 + I2 + I4 + I7)) and ((W . take_turns) in I2) and true) or (((W . line) in I3) and ((W . thirdparty_actions') in I1)) or (((W . thirdparty_actions') in I2) and ((W . line) in I5))) and ((((W . receiver_actions') in I0) and ((W . take_turns) in (I0 + I2))) or (((W . take_turns) in I1) and true)) and ((((W . take_turns) in (I1 + I2)) and ((W . sender_actions') in I0)) or (true and ((W . take_turns) in I0))) and (((((W . sender_actions) in I4) or ((W . line) in (I1 + I3 + I4 + I5 + I6 + I7))) and (((W . line) in (I2 + I3 + I4 + I5 + I6 + I7)) or ((W . sender_actions) in (I0 + I1 + I3 + I4))) and ((W . line') in I6) and (((W . sender_actions) in (I0 + I1 + I2 + I3)) or ((W . line) in (I1 + I3 + I4 + I5 + I6 + I7))) and (((W . sender_actions) in I2) or ((W . line) in (I2 + I3 + I4 + I5 + I6 + I7))) and (((W . receiver_actions) in I2) or ((W . line) in (I1 + I2 + I3 + I5 + I6 + I7))) and (((W . receiver_actions) in (I0 + I1)) or ((W . line) in (I1 + I2 + I3 + I5 + I6 + I7))) and ((W . line) in I5)) or ((((W . sender_actions) in I4) or ((W . line) in (I1 + I3 + I4 + I5 + I6 + I7))) and ((W . sender_actions) in I4) and (((W . line) in (I2 + I3 + I4 + I5 + I6 + I7)) or ((W . sender_actions) in (I0 + I1 + I3 + I4))) and ((W . line') in I3) and (((W . sender_actions) in I2) or ((W . line) in (I2 + I3 + I4 + I5 + I6 + I7))) and ((W . line) in I2)) or (((W . line) in I1) and ((W . sender_actions) in (I0 + I1 + I3 + I4)) and ((W . line') in I1)) or ((((W . sender_actions) in I4) or ((W . line) in (I1 + I3 + I4 + I5 + I6 + I7))) and (((W . line) in (I2 + I3 + I4 + I5 + I6 + I7)) or ((W . sender_actions) in (I0 + I1 + I3 + I4))) and ((W . line') in I7) and (((W . sender_actions) in (I0 + I1 + I2 + I3)) or ((W . line) in (I1 + I3 + I4 + I5 + I6 + I7))) and (((W . sender_actions) in I2) or ((W . line) in (I2 + I3 + I4 + I5 + I6 + I7))) and (((W . receiver_actions) in I2) or ((W . line) in (I1 + I2 + I3 + I5 + I6 + I7))) and (((W . receiver_actions) in (I0 + I1)) or ((W . line) in (I1 + I2 + I3 + I5 + I6 + I7))) and ((W . line) in I7)) or ((((W . sender_actions) in I4) or ((W . line) in (I1 + I3 + I4 + I5 + I6 + I7))) and (((W . line) in (I2 + I3 + I4 + I5 + I6 + I7)) or ((W . sender_actions) in (I0 + I1 + I3 + I4))) and ((W . receiver_actions) in I2) and ((W . line) in I4) and (((W . sender_actions) in (I0 + I1 + I2 + I3)) or ((W . line) in (I1 + I3 + I4 + I5 + I6 + I7))) and ((W . line') in I5) and (((W . sender_actions) in I2) or ((W . line) in (I2 + I3 + I4 + I5 + I6 + I7))) and (((W . receiver_actions) in I2) or ((W . line) in (I1 + I2 + I3 + I5 + I6 + I7)))) or (((W . line') in I4) and (((W . sender_actions) in I4) or ((W . line) in (I1 + I3 + I4 + I5 + I6 + I7))) and (((W . line) in (I2 + I3 + I4 + I5 + I6 + I7)) or ((W . sender_actions) in (I0 + I1 + I3 + I4))) and (((W . sender_actions) in (I0 + I1 + I2 + I3)) or ((W . line) in (I1 + I3 + I4 + I5 + I6 + I7))) and ((W . line) in I3) and (((W . sender_actions) in I2) or ((W . line) in (I2 + I3 + I4 + I5 + I6 + I7)))) or (((W . line') in I2) and (((W . line) in (I2 + I3 + I4 + I5 + I6 + I7)) or ((W . sender_actions) in (I0 + I1 + I3 + I4))) and ((W . sender_actions) in (I0 + I1 + I2 + I3)) and (((W . sender_actions) in I2) or ((W . line) in (I2 + I3 + I4 + I5 + I6 + I7))) and ((W . line) in I2)) or ((((W . sender_actions) in I4) or ((W . line) in (I1 + I3 + I4 + I5 + I6 + I7))) and ((W . line) in I6) and (((W . line) in (I2 + I3 + I4 + I5 + I6 + I7)) or ((W . sender_actions) in (I0 + I1 + I3 + I4))) and ((W . line') in I7) and (((W . sender_actions) in (I0 + I1 + I2 + I3)) or ((W . line) in (I1 + I3 + I4 + I5 + I6 + I7))) and (((W . sender_actions) in I2) or ((W . line) in (I2 + I3 + I4 + I5 + I6 + I7))) and (((W . receiver_actions) in I2) or ((W . line) in (I1 + I2 + I3 + I5 + I6 + I7))) and (((W . receiver_actions) in (I0 + I1)) or ((W . line) in (I1 + I2 + I3 + I5 + I6 + I7)))) or (((W . line) in I1) and ((W . sender_actions) in I2) and ((W . line') in I2) and (((W . sender_actions) in I2) or ((W . line) in (I2 + I3 + I4 + I5 + I6 + I7)))) or (((W . line') in I4) and (((W . sender_actions) in I4) or ((W . line) in (I1 + I3 + I4 + I5 + I6 + I7))) and ((W . receiver_actions) in (I0 + I1)) and (((W . line) in (I2 + I3 + I4 + I5 + I6 + I7)) or ((W . sender_actions) in (I0 + I1 + I3 + I4))) and ((W . line) in I4) and (((W . sender_actions) in (I0 + I1 + I2 + I3)) or ((W . line) in (I1 + I3 + I4 + I5 + I6 + I7))) and (((W . sender_actions) in I2) or ((W . line) in (I2 + I3 + I4 + I5 + I6 + I7))))) and ((((W . take_turns') = (W . take_turns)) and ((W . line) in I7)) or (((W . take_turns) in I1) and ((W . take_turns') in I2) and ((W . line) in (I1 + I2 + I4 + I5))) or (((W . line) in I6) and ((W . take_turns') = (W . take_turns))) or (((W . line) in I3) and ((W . take_turns') = (W . take_turns))) or (((W . take_turns') in I1) and ((W . line) in (I1 + I2 + I4 + I5)) and ((W . take_turns) in I0)) or (((W . take_turns') in I0) and ((W . take_turns) in I2) and ((W . line) in (I1 + I2 + I4 + I5)))))
  }
/* 
  State machine
  */
pred FSM[W : Main] {
  (init_0[W]) and (invar5[W]) and (range_line[W]) and (range_receiver_actions[W]) and (range_sender_actions[W]) and (range_take_turns[W]) and (range_thirdparty_actions[W]) and (trans0[W])
  }
/* 
  Auxiliary model definitions
  */