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
one sig Im1 , I0 , I1 , I2 , I3 extends I {
  }
fun minusI[_i1 : I , _i2 : I] : I {
  ((Im1 -> Im1 -> I0) + (Im1 -> I0 -> Im1) + (I0 -> Im1 -> I1) + (I0 -> I0 -> I0) + (I0 -> I1 -> Im1) + (I1 -> Im1 -> I2) + (I1 -> I0 -> I1) + (I1 -> I1 -> I0) + (I1 -> I2 -> Im1) + (I2 -> Im1 -> I3) + (I2 -> I0 -> I2) + (I2 -> I1 -> I1) + (I2 -> I2 -> I0) + (I2 -> I3 -> Im1) + (I3 -> I0 -> I3) + (I3 -> I1 -> I2) + (I3 -> I2 -> I1) + (I3 -> I3 -> I0))[_i1 , _i2]
  }
sig I_0_2 = I0 + I1 + I2 {}
sig I_0_3 = I0 + I1 + I2 + I3 {}
/* 
  ********** Model starts here **********
  */
/* 
  Model
  */
trace sig Main {
  var action : one I_0_2,
  var beverage : one I_0_2,
  var mutation : one B,
  var water : one I_0_3,
  var NO_output : one B,
  var NO_water : one B }
/* 
  Initial states
  */
pred init_0[W : Main] {
  ((W . action) = I0) and ((W . beverage) = I0) and ((W . water) = I2)
  }
/* 
  Invariants
  */
pred range_action[W : Main] {
  always ((W . action) in (I0 + I1 + I2))
  }
pred range_beverage[W : Main] {
  always ((W . beverage) in (I0 + I1 + I2))
  }
pred range_water[W : Main] {
  always ((W . water) in (I0 + I1 + I2 + I3))
  }
pred define_NO_output[W : Main] {
  always (((W . NO_output) = T) iff ((((W . action) = I1) and ((W . beverage) = I0)) or (not ((W . action) = I1))))
  }
pred define_NO_water[W : Main] {
  always (((W . NO_water) = T) iff (((W . action) = I1) and ((W . water) = I0)))
  }
pred invar5[W : Main] {
  always (true)
  }
/* 
  State transitions
  */
pred trans0[W : Main] {
  always (((((not ((W . action) = I1)) or ((W . water) = I0)) and ((W . water') = I1) and ((W . water) = I0) and ((W . mutation) = T)) or (((W . action) = I1) and ((W . water') in (minusI[W . water , I1])) and (not ((W . water) = I0))) or (((not ((W . mutation) = T)) or (not ((W . water) = I0))) and ((not ((W . action) = I1)) or ((W . water) = I0)) and ((W . water) = I1) and ((W . water') = I2) and ((W . mutation) = T)) or ((not ((W . mutation) = T)) and ((not ((W . mutation) = T)) or (not ((W . water) = I0))) and ((W . water') = I3) and ((not ((W . action) = I1)) or ((W . water) = I0)) and ((not ((W . mutation) = T)) or (not ((W . water) = I1))) and ((not ((W . mutation) = T)) or (not ((W . water) = I3))) and ((W . water) = I2) and ((not ((W . water) = I1)) or ((W . mutation) = T)) and ((not ((W . water) = I0)) or ((W . mutation) = T)) and ((not ((W . mutation) = T)) or (not ((W . water) = I2)))) or ((not ((W . mutation) = T)) and ((not ((W . mutation) = T)) or (not ((W . water) = I0))) and ((not ((W . action) = I1)) or ((W . water) = I0)) and ((not ((W . mutation) = T)) or (not ((W . water) = I1))) and ((not ((W . mutation) = T)) or (not ((W . water) = I3))) and ((W . water') = I2) and ((W . water) = I0) and ((not ((W . mutation) = T)) or (not ((W . water) = I2)))) or (((not ((W . mutation) = T)) or (not ((W . water) = I0))) and ((W . water') = I3) and ((not ((W . action) = I1)) or ((W . water) = I0)) and ((not ((W . mutation) = T)) or (not ((W . water) = I1))) and ((W . water) = I2) and ((W . mutation) = T)) or (((not ((W . mutation) = T)) or (not ((W . water) = I0))) and ((not ((W . water) = I3)) or ((W . mutation) = T)) and ((not ((W . action) = I1)) or ((W . water) = I0)) and ((not ((W . mutation) = T)) or (not ((W . water) = I1))) and ((W . water') in (W . water)) and ((not ((W . water) = I2)) or ((W . mutation) = T)) and ((not ((W . mutation) = T)) or (not ((W . water) = I3))) and ((not ((W . water) = I1)) or ((W . mutation) = T)) and ((not ((W . water) = I0)) or ((W . mutation) = T)) and ((not ((W . mutation) = T)) or (not ((W . water) = I2)))) or ((not ((W . mutation) = T)) and ((not ((W . mutation) = T)) or (not ((W . water) = I0))) and ((W . water') = I3) and ((not ((W . action) = I1)) or ((W . water) = I0)) and ((not ((W . mutation) = T)) or (not ((W . water) = I1))) and ((W . water) = I1) and ((not ((W . mutation) = T)) or (not ((W . water) = I3))) and ((not ((W . water) = I0)) or ((W . mutation) = T)) and ((not ((W . mutation) = T)) or (not ((W . water) = I2)))) or (((not ((W . mutation) = T)) or (not ((W . water) = I0))) and ((W . water') = I3) and ((not ((W . action) = I1)) or ((W . water) = I0)) and ((not ((W . mutation) = T)) or (not ((W . water) = I1))) and ((not ((W . mutation) = T)) or (not ((W . water) = I2))) and ((W . water) = I3) and ((W . mutation) = T)) or ((not ((W . mutation) = T)) and ((not ((W . mutation) = T)) or (not ((W . water) = I0))) and ((W . water') = I3) and ((not ((W . action) = I1)) or ((W . water) = I0)) and ((not ((W . mutation) = T)) or (not ((W . water) = I1))) and ((not ((W . water) = I2)) or ((W . mutation) = T)) and ((not ((W . mutation) = T)) or (not ((W . water) = I3))) and ((not ((W . water) = I1)) or ((W . mutation) = T)) and ((not ((W . water) = I0)) or ((W . mutation) = T)) and ((not ((W . mutation) = T)) or (not ((W . water) = I2))) and ((W . water) = I3))) and ((((not ((W . action) = I1)) or ((W . water) = I0)) and ((W . beverage') in (W . beverage))) or (((W . action) = I1) and (not ((W . water) = I0)) and ((W . beverage') = I1))))
  }
/* 
  State machine
  */
pred FSM[W : Main] {
  (define_NO_output[W]) and (define_NO_water[W]) and (init_0[W]) and (invar5[W]) and (range_action[W]) and (range_beverage[W]) and (range_water[W]) and (trans0[W])
  }
/* 
  Auxiliary model definitions
  */