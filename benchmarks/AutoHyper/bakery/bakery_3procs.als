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
one sig I0 , I1 , I2 , I3 , I4 extends I {
  }
pred leqI[_i1 : I , _i2 : I] {
  (_i1 -> _i2) in ((I0 -> I0) + (I0 -> I1) + (I0 -> I2) + (I0 -> I3) + (I0 -> I4) + (I1 -> I1) + (I1 -> I2) + (I1 -> I3) + (I1 -> I4) + (I2 -> I2) + (I2 -> I3) + (I2 -> I4) + (I3 -> I3) + (I3 -> I4) + (I4 -> I4))
  }
fun plusI[_i1 : I , _i2 : I] : I {
  ((I0 -> I0 -> I0) + (I0 -> I1 -> I1) + (I0 -> I2 -> I2) + (I0 -> I3 -> I3) + (I0 -> I4 -> I4) + (I1 -> I0 -> I1) + (I1 -> I1 -> I2) + (I1 -> I2 -> I3) + (I1 -> I3 -> I4) + (I2 -> I0 -> I2) + (I2 -> I1 -> I3) + (I2 -> I2 -> I4) + (I3 -> I0 -> I3) + (I3 -> I1 -> I4) + (I4 -> I0 -> I4))[_i1 , _i2]
  }
sig I_0_3 = I0 + I1 + I2 + I3 {}
sig I_0_4 = I0 + I1 + I2 + I3 + I4 {}
/* 
  ********** Model starts here **********
  */
/* 
  Model
  */
trace sig Main {
  var MAX_ticket : one I_0_3,
  var p1_line : one I_0_4,
  var p1_ticket : one I_0_3,
  var p2_line : one I_0_4,
  var p2_ticket : one I_0_3,
  var p3_line : one I_0_4,
  var p3_ticket : one I_0_3,
  var STARTED : one B,
  var p1_TOKEN : one B,
  var p2_TOKEN : one B,
  var p3_TOKEN : one B }
/* 
  Initial states
  */
pred init_0[W : Main] {
  ((W . p3_line) = I0) and ((W . p3_ticket) = I3) and ((W . p1_ticket) = I3) and ((W . p2_line) = I0) and ((W . p1_line) = I0) and ((W . MAX_ticket) = I0) and ((W . p2_ticket) = I3)
  }
/* 
  Invariants
  */
pred range_MAX_ticket[W : Main] {
  always ((W . MAX_ticket) in (I0 + I1 + I2 + I3))
  }
pred range_p1_line[W : Main] {
  always ((W . p1_line) in (I0 + I1 + I2 + I3 + I4))
  }
pred range_p1_ticket[W : Main] {
  always ((W . p1_ticket) in (I0 + I1 + I2 + I3))
  }
pred range_p2_line[W : Main] {
  always ((W . p2_line) in (I0 + I1 + I2 + I3 + I4))
  }
pred range_p2_ticket[W : Main] {
  always ((W . p2_ticket) in (I0 + I1 + I2 + I3))
  }
pred range_p3_line[W : Main] {
  always ((W . p3_line) in (I0 + I1 + I2 + I3 + I4))
  }
pred range_p3_ticket[W : Main] {
  always ((W . p3_ticket) in (I0 + I1 + I2 + I3))
  }
pred define_STARTED[W : Main] {
  always (((W . STARTED) = T) iff ((not ((W . p3_line) = I0)) or (not ((W . p2_line) = I0)) or (not ((W . p1_line) = I0))))
  }
pred define_p1_TOKEN[W : Main] {
  always (((W . p1_TOKEN) = T) iff (((W . p1_line) = I2) and ((W . STARTED) = T) and (leqI[W . p1_ticket , W . p3_ticket]) and (leqI[W . p1_ticket , W . p2_ticket])))
  }
pred define_p2_TOKEN[W : Main] {
  always (((W . p2_TOKEN) = T) iff (((W . p2_line) = I2) and (((leqI[W . p2_ticket , W . p3_ticket]) and (leqI[W . p2_ticket , W . p1_ticket])) or (not ((W . p1_TOKEN) = T))) and ((W . STARTED) = T)))
  }
pred define_p3_TOKEN[W : Main] {
  always (((W . p3_TOKEN) = T) iff (((W . p3_line) = I2) and ((W . STARTED) = T) and (((not ((W . p1_TOKEN) = T)) and (not ((W . p2_TOKEN) = T))) or ((leqI[W . p3_ticket , W . p2_ticket]) and (leqI[W . p3_ticket , W . p1_ticket])))))
  }
pred invar11[W : Main] {
  always (true)
  }
/* 
  State transitions
  */
pred trans0[W : Main] {
  always ((((not ((W . MAX_ticket) = I3)) and (not ((W . p3_line) = I1)) and (not ((W . p2_line) = I1)) and ((W . MAX_ticket') in (W . MAX_ticket)) and (not ((W . p1_line) = I1))) or ((((W . p3_line) = I1) or ((W . p2_line) = I1) or ((W . p1_line) = I1)) and (not ((W . MAX_ticket) = I3)) and ((W . MAX_ticket') in (plusI[W . MAX_ticket , I1]))) or (((W . MAX_ticket') = I0) and ((W . MAX_ticket) = I3))) and (((not ((W . MAX_ticket) = I3)) and ((W . p1_ticket') in (plusI[W . MAX_ticket , I1])) and ((W . p1_line) = I1)) or ((not ((W . MAX_ticket) = I3)) and ((W . p1_ticket') in (W . p1_ticket)) and (not ((W . p1_line) = I1))) or (((W . p1_ticket') = I0) and ((W . MAX_ticket) = I3))) and ((((W . p2_line') = I0) and ((not ((W . p2_line) = I2)) or (not ((W . p2_TOKEN) = T))) and (((W . p2_TOKEN) = T) or (not ((W . p2_line) = I2))) and ((W . p2_line) = I4)) or (((W . p2_line) = I2) and ((not ((W . p2_line) = I2)) or (not ((W . p2_TOKEN) = T))) and (((W . p2_TOKEN) = T) or (not ((W . p2_line) = I2))) and ((W . p2_line') in (W . p2_line))) or (((W . p2_line) = I0) and ((W . p2_line') in (I0 + I1))) or (((W . p2_line) = I2) and ((W . p2_line') = I3) and (((W . p2_TOKEN) = T) or (not ((W . p2_line) = I2))) and ((W . p2_TOKEN) = T)) or (((W . p2_line') = I2) and ((W . p2_line) = I1)) or (((W . p2_line') = I2) and ((W . p2_line) = I2) and (not ((W . p2_TOKEN) = T))) or (((W . p2_line') = I4) and ((W . p2_line) = I3) and ((not ((W . p2_line) = I2)) or (not ((W . p2_TOKEN) = T))) and (((W . p2_TOKEN) = T) or (not ((W . p2_line) = I2))))) and ((((W . p1_line') = I0) and ((W . p1_line) = I4) and ((not ((W . p1_line) = I2)) or ((W . p1_TOKEN) = T)) and ((not ((W . p1_line) = I2)) or (not ((W . p1_TOKEN) = T)))) or (((W . p1_line) = I2) and (not ((W . p1_TOKEN) = T)) and ((W . p1_line') = I2)) or (((W . p1_line) = I2) and ((not ((W . p1_line) = I2)) or ((W . p1_TOKEN) = T)) and ((W . p1_line') in (W . p1_line)) and ((not ((W . p1_line) = I2)) or (not ((W . p1_TOKEN) = T)))) or (((W . p1_line) = I2) and ((W . p1_line') = I3) and ((W . p1_TOKEN) = T) and ((not ((W . p1_line) = I2)) or ((W . p1_TOKEN) = T))) or (((W . p1_line') = I2) and ((W . p1_line) = I1)) or (((W . p1_line) = I0) and ((W . p1_line') in (I0 + I1))) or (((W . p1_line') = I4) and ((W . p1_line) = I3) and ((not ((W . p1_line) = I2)) or ((W . p1_TOKEN) = T)) and ((not ((W . p1_line) = I2)) or (not ((W . p1_TOKEN) = T))))) and ((((W . p3_ticket') = I0) and ((W . MAX_ticket) = I3)) or (((W . p3_ticket') in (plusI[W . MAX_ticket , I1])) and (not ((W . MAX_ticket) = I3)) and ((W . p3_line) = I1)) or ((not ((W . MAX_ticket) = I3)) and ((W . p3_ticket') in (W . p3_ticket)) and (not ((W . p3_line) = I1)))) and ((((W . p2_ticket') = I0) and ((W . MAX_ticket) = I3)) or (((W . p2_ticket') in (plusI[W . MAX_ticket , I1])) and (not ((W . MAX_ticket) = I3)) and ((W . p2_line) = I1)) or (((W . p2_ticket') in (W . p2_ticket)) and (not ((W . MAX_ticket) = I3)) and (not ((W . p2_line) = I1)))) and ((((not ((W . p3_line) = I2)) or (not ((W . p3_TOKEN) = T))) and ((W . p3_line) = I4) and ((W . p3_line') = I0) and (((W . p3_TOKEN) = T) or (not ((W . p3_line) = I2)))) or (((W . p3_line) = I0) and ((W . p3_line') = I0)) or (((W . p3_line) = I3) and ((not ((W . p3_line) = I2)) or (not ((W . p3_TOKEN) = T))) and (((W . p3_TOKEN) = T) or (not ((W . p3_line) = I2))) and ((W . p3_line') = I4)) or (((not ((W . p3_line) = I2)) or (not ((W . p3_TOKEN) = T))) and ((W . p3_line) = I2) and (((W . p3_TOKEN) = T) or (not ((W . p3_line) = I2))) and ((W . p3_line') in (W . p3_line))) or (((W . p3_line') = I2) and ((W . p3_line) = I1)) or (((W . p3_line') = I2) and ((W . p3_line) = I2) and (not ((W . p3_TOKEN) = T))) or (((W . p3_TOKEN) = T) and ((W . p3_line) = I2) and (((W . p3_TOKEN) = T) or (not ((W . p3_line) = I2))) and ((W . p3_line') = I3))))
  }
/* 
  State machine
  */
pred FSM[W : Main] {
  (define_STARTED[W]) and (define_p1_TOKEN[W]) and (define_p2_TOKEN[W]) and (define_p3_TOKEN[W]) and (init_0[W]) and (invar11[W]) and (range_MAX_ticket[W]) and (range_p1_line[W]) and (range_p1_ticket[W]) and (range_p2_line[W]) and (range_p2_ticket[W]) and (range_p3_line[W]) and (range_p3_ticket[W]) and (trans0[W])
  }
/* 
  Auxiliary model definitions
  */