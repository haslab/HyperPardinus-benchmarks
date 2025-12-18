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
one sig I0 , I1 , I2 , I3 , I4 , I5 , I6 extends I {
  }
sig I_0_1 = I0 + I1 {}
sig I_0_2 = I0 + I1 + I2 {}
sig I_0_6 = I0 + I1 + I2 + I3 + I4 + I5 + I6 {}
/* 
  ********** Model starts here **********
  */
/* 
  Model
  */
trace sig Main {
  var MASK_0 : one I_0_1,
  var MASK_1 : one I_0_1,
  var MASK_2 : one I_0_1,
  var PIN_0 : one I_0_1,
  var PIN_1 : one I_0_1,
  var PIN_2 : one I_0_1,
  var RESULT_0 : one I_0_1,
  var RESULT_1 : one I_0_1,
  var RESULT_2 : one I_0_1,
  var alpha_line : one I_0_6,
  var beta_line : one I_0_6,
  var main_trigger : one I_0_2,
  var theta_line : one I_0_6,
  var trigger_alpha : one B,
  var trigger_beta : one B,
  var halt : one B }
/* 
  Initial states
  */
pred init_0[W : Main] {
  (not ((W . trigger_beta) = T)) and ((W . beta_line) = I0) and (not ((W . trigger_alpha) = T)) and ((W . RESULT_0) = I0) and ((W . RESULT_1) = I0) and ((W . MASK_2) = I0) and ((W . MASK_0) = I1) and ((W . RESULT_2) = I0) and ((W . main_trigger) = I0) and ((W . PIN_2) = I1) and ((W . alpha_line) = I0) and ((W . theta_line) = I0) and ((W . MASK_1) = I0)
  }
/* 
  Invariants
  */
pred range_MASK_0[W : Main] {
  always ((W . MASK_0) in (I0 + I1))
  }
pred range_MASK_1[W : Main] {
  always ((W . MASK_1) in (I0 + I1))
  }
pred range_MASK_2[W : Main] {
  always ((W . MASK_2) in (I0 + I1))
  }
pred range_PIN_0[W : Main] {
  always ((W . PIN_0) in (I0 + I1))
  }
pred range_PIN_1[W : Main] {
  always ((W . PIN_1) in (I0 + I1))
  }
pred range_PIN_2[W : Main] {
  always ((W . PIN_2) in (I0 + I1))
  }
pred range_RESULT_0[W : Main] {
  always ((W . RESULT_0) in (I0 + I1))
  }
pred range_RESULT_1[W : Main] {
  always ((W . RESULT_1) in (I0 + I1))
  }
pred range_RESULT_2[W : Main] {
  always ((W . RESULT_2) in (I0 + I1))
  }
pred range_alpha_line[W : Main] {
  always ((W . alpha_line) in (I0 + I1 + I2 + I3 + I4 + I5 + I6))
  }
pred range_beta_line[W : Main] {
  always ((W . beta_line) in (I0 + I1 + I2 + I3 + I4 + I5 + I6))
  }
pred range_main_trigger[W : Main] {
  always ((W . main_trigger) in (I0 + I1 + I2))
  }
pred range_theta_line[W : Main] {
  always ((W . theta_line) in (I0 + I1 + I2 + I3 + I4 + I5 + I6))
  }
pred define_halt[W : Main] {
  always (((W . halt) = T) iff (((W . MASK_2) = I0) and ((W . MASK_0) = I0) and ((W . theta_line) = I0) and ((W . MASK_1) = I0)))
  }
pred invar14[W : Main] {
  always (true)
  }
/* 
  State transitions
  */
pred trans0[W : Main] {
  always (((((((W . MASK_2) = I0) and ((W . RESULT_2) = I0)) or (not ((W . alpha_line) = I2))) and ((W . RESULT_2') = I0) and ((W . MASK_2) = I0) and ((W . RESULT_2) = I0) and ((W . alpha_line) = I2)) or (((((W . MASK_2) = I0) and ((W . RESULT_2) = I0)) or (not ((W . alpha_line) = I2))) and ((W . RESULT_2) = I1) and ((W . beta_line) = I2) and ((W . RESULT_2') = I1) and ((W . MASK_2) = I0) and (((W . RESULT_2) = I1) or ((W . MASK_2) = I1) or (not ((W . alpha_line) = I2)))) or (((((W . MASK_2) = I0) and ((W . RESULT_2) = I0)) or (not ((W . alpha_line) = I2))) and ((W . RESULT_2') = I0) and ((W . beta_line) = I2) and (((W . RESULT_2) = I1) or ((W . MASK_2) = I1) or (not ((W . alpha_line) = I2))) and (((W . MASK_2) = I1) or ((W . RESULT_2) = I0) or (not ((W . beta_line) = I2))) and (((W . MASK_2) = I1) or ((W . RESULT_2) = I0))) or ((((W . RESULT_2) = I1) or ((W . MASK_2) = I1)) and ((W . RESULT_2') = I1) and ((W . alpha_line) = I2)) or (((((W . MASK_2) = I0) and ((W . RESULT_2) = I0)) or (not ((W . alpha_line) = I2))) and ((((W . RESULT_2) = I1) and ((W . MASK_2) = I0)) or (not ((W . beta_line) = I2))) and (((W . RESULT_2) = I1) or ((W . MASK_2) = I1) or (not ((W . alpha_line) = I2))) and (((W . MASK_2) = I1) or ((W . RESULT_2) = I0) or (not ((W . beta_line) = I2))) and ((W . RESULT_2') in (W . RESULT_2)))) and ((((not ((W . theta_line) = I2)) or (((W . PIN_0) = (W . MASK_0)) and ((W . PIN_2) = (W . MASK_2)) and ((W . PIN_1) = (W . MASK_1)))) and ((not ((W . theta_line) = I0)) or (((W . MASK_2) = I0) and ((W . MASK_0) = I0) and ((W . MASK_1) = I0))) and ((not ((W . theta_line) = I2)) or (not ((W . PIN_2) = (W . MASK_2))) or (not ((W . PIN_1) = (W . MASK_1))) or (not ((W . PIN_0) = (W . MASK_0)))) and ((W . theta_line') = I5) and (((W . MASK_2) = I1) or (not ((W . theta_line) = I0)) or ((W . MASK_0) = I1) or ((W . MASK_1) = I1)) and ((W . theta_line) = I4)) or (((not ((W . theta_line) = I5)) or ((W . main_trigger) = I2)) and ((not ((W . theta_line) = I2)) or (((W . PIN_0) = (W . MASK_0)) and ((W . PIN_2) = (W . MASK_2)) and ((W . PIN_1) = (W . MASK_1)))) and ((not ((W . theta_line) = I0)) or (((W . MASK_2) = I0) and ((W . MASK_0) = I0) and ((W . MASK_1) = I0))) and ((W . theta_line') = I0) and ((W . theta_line) = I6) and ((not ((W . theta_line) = I2)) or (not ((W . PIN_2) = (W . MASK_2))) or (not ((W . PIN_1) = (W . MASK_1))) or (not ((W . PIN_0) = (W . MASK_0)))) and ((not ((W . main_trigger) = I2)) or (not ((W . theta_line) = I5))) and (((W . MASK_2) = I1) or (not ((W . theta_line) = I0)) or ((W . MASK_0) = I1) or ((W . MASK_1) = I1))) or (((W . theta_line) = I1) and ((W . theta_line') = I2) and ((not ((W . theta_line) = I0)) or (((W . MASK_2) = I0) and ((W . MASK_0) = I0) and ((W . MASK_1) = I0))) and (((W . MASK_2) = I1) or (not ((W . theta_line) = I0)) or ((W . MASK_0) = I1) or ((W . MASK_1) = I1))) or (((W . theta_line') = I1) and (((W . MASK_2) = I1) or ((W . MASK_0) = I1) or ((W . MASK_1) = I1)) and ((W . theta_line) = I0) and (((W . MASK_2) = I1) or (not ((W . theta_line) = I0)) or ((W . MASK_0) = I1) or ((W . MASK_1) = I1))) or (((not ((W . theta_line) = I5)) or ((W . main_trigger) = I2)) and ((W . theta_line') = I6) and ((not ((W . theta_line) = I2)) or (((W . PIN_0) = (W . MASK_0)) and ((W . PIN_2) = (W . MASK_2)) and ((W . PIN_1) = (W . MASK_1)))) and ((W . theta_line) = I5) and ((not ((W . theta_line) = I0)) or (((W . MASK_2) = I0) and ((W . MASK_0) = I0) and ((W . MASK_1) = I0))) and ((W . main_trigger) = I2) and ((not ((W . theta_line) = I2)) or (not ((W . PIN_2) = (W . MASK_2))) or (not ((W . PIN_1) = (W . MASK_1))) or (not ((W . PIN_0) = (W . MASK_0)))) and (((W . MASK_2) = I1) or (not ((W . theta_line) = I0)) or ((W . MASK_0) = I1) or ((W . MASK_1) = I1))) or (((not ((W . PIN_2) = (W . MASK_2))) or (not ((W . PIN_1) = (W . MASK_1))) or (not ((W . PIN_0) = (W . MASK_0)))) and ((W . theta_line) = I2) and ((not ((W . theta_line) = I0)) or (((W . MASK_2) = I0) and ((W . MASK_0) = I0) and ((W . MASK_1) = I0))) and ((W . theta_line') = I4) and ((not ((W . theta_line) = I2)) or (not ((W . PIN_2) = (W . MASK_2))) or (not ((W . PIN_1) = (W . MASK_1))) or (not ((W . PIN_0) = (W . MASK_0)))) and (((W . MASK_2) = I1) or (not ((W . theta_line) = I0)) or ((W . MASK_0) = I1) or ((W . MASK_1) = I1))) or (((W . PIN_0) = (W . MASK_0)) and ((W . PIN_2) = (W . MASK_2)) and ((W . theta_line) = I2) and ((not ((W . theta_line) = I0)) or (((W . MASK_2) = I0) and ((W . MASK_0) = I0) and ((W . MASK_1) = I0))) and ((W . theta_line') = I3) and ((W . PIN_1) = (W . MASK_1)) and (((W . MASK_2) = I1) or (not ((W . theta_line) = I0)) or ((W . MASK_0) = I1) or ((W . MASK_1) = I1))) or (((W . MASK_2) = I0) and ((W . theta_line') = I0) and ((W . MASK_0) = I0) and ((W . theta_line) = I0) and ((W . MASK_1) = I0)) or (((W . theta_line) = I3) and ((not ((W . theta_line) = I0)) or (((W . MASK_2) = I0) and ((W . MASK_0) = I0) and ((W . MASK_1) = I0))) and ((not ((W . theta_line) = I2)) or (not ((W . PIN_2) = (W . MASK_2))) or (not ((W . PIN_1) = (W . MASK_1))) or (not ((W . PIN_0) = (W . MASK_0)))) and ((W . theta_line') = I5) and (((W . MASK_2) = I1) or (not ((W . theta_line) = I0)) or ((W . MASK_0) = I1) or ((W . MASK_1) = I1))) or ((not ((W . main_trigger) = I2)) and ((not ((W . theta_line) = I2)) or (((W . PIN_0) = (W . MASK_0)) and ((W . PIN_2) = (W . MASK_2)) and ((W . PIN_1) = (W . MASK_1)))) and ((W . theta_line) = I5) and ((not ((W . theta_line) = I0)) or (((W . MASK_2) = I0) and ((W . MASK_0) = I0) and ((W . MASK_1) = I0))) and ((not ((W . theta_line) = I2)) or (not ((W . PIN_2) = (W . MASK_2))) or (not ((W . PIN_1) = (W . MASK_1))) or (not ((W . PIN_0) = (W . MASK_0)))) and ((W . theta_line') = I5) and (((W . MASK_2) = I1) or (not ((W . theta_line) = I0)) or ((W . MASK_0) = I1) or ((W . MASK_1) = I1)))) and ((((W . MASK_2) = I1) and ((W . theta_line) = I6) and ((W . MASK_1') = I1)) or (((W . MASK_1') = I0) and ((W . theta_line) = I6) and ((W . MASK_1) = I1) and (((W . MASK_2) = I0) or (not ((W . theta_line) = I6)))) or (((not ((W . theta_line) = I6)) or ((W . MASK_1) = I0)) and ((W . MASK_1') in (W . MASK_1)) and (((W . MASK_2) = I0) or (not ((W . theta_line) = I6))))) and ((((not ((W . beta_line) = I4)) or (not ((W . main_trigger) = I0))) and ((W . main_trigger') = I2) and (not ((W . theta_line) = I1)) and ((W . beta_line) = I4) and ((not ((W . alpha_line) = I4)) or (not ((W . main_trigger) = I0))) and ((W . main_trigger) = I1) and ((not ((W . alpha_line) = I4)) or (not ((W . main_trigger) = I1)))) or ((not ((W . theta_line) = I1)) and ((W . main_trigger) = I0) and ((W . beta_line) = I4) and ((not ((W . alpha_line) = I4)) or (not ((W . main_trigger) = I0))) and ((W . main_trigger') = I1) and ((not ((W . alpha_line) = I4)) or (not ((W . main_trigger) = I1)))) or (((not ((W . beta_line) = I4)) or (not ((W . main_trigger) = I0))) and (not ((W . theta_line) = I1)) and ((not ((W . beta_line) = I4)) or (not ((W . main_trigger) = I1))) and ((not ((W . alpha_line) = I4)) or (not ((W . main_trigger) = I0))) and ((W . main_trigger') in (W . main_trigger)) and ((not ((W . alpha_line) = I4)) or (not ((W . main_trigger) = I1)))) or (((W . theta_line) = I1) and ((W . main_trigger') = I0)) or ((not ((W . theta_line) = I1)) and ((W . main_trigger) = I0) and ((W . main_trigger') = I1) and ((W . alpha_line) = I4)) or (((W . main_trigger') = I2) and (not ((W . theta_line) = I1)) and ((not ((W . alpha_line) = I4)) or (not ((W . main_trigger) = I0))) and ((W . main_trigger) = I1) and ((W . alpha_line) = I4))) and ((((not ((W . beta_line) = I0)) or (((W . MASK_2) = I0) and ((W . MASK_0) = I0) and ((W . MASK_1) = I0))) and ((not ((W . trigger_beta) = T)) or (not ((W . beta_line) = I1))) and ((W . beta_line') = I0) and (((W . MASK_2) = I1) or (not ((W . beta_line) = I0)) or ((W . MASK_0) = I1) or ((W . MASK_1) = I1)) and ((W . beta_line) = I6) and ((not ((W . beta_line) = I1)) or (not (not ((W . trigger_beta) = T))))) or (((W . beta_line') = I1) and (not ((W . trigger_beta) = T)) and ((not ((W . beta_line) = I0)) or (((W . MASK_2) = I0) and ((W . MASK_0) = I0) and ((W . MASK_1) = I0))) and ((W . beta_line) = I1) and (((W . MASK_2) = I1) or (not ((W . beta_line) = I0)) or ((W . MASK_0) = I1) or ((W . MASK_1) = I1))) or (((not ((W . beta_line) = I0)) or (((W . MASK_2) = I0) and ((W . MASK_0) = I0) and ((W . MASK_1) = I0))) and ((not ((W . trigger_beta) = T)) or (not ((W . beta_line) = I1))) and (((W . MASK_2) = I1) or (not ((W . beta_line) = I0)) or ((W . MASK_0) = I1) or ((W . MASK_1) = I1)) and ((W . beta_line) = I3) and ((W . beta_line') = I4) and ((not ((W . beta_line) = I1)) or (not (not ((W . trigger_beta) = T))))) or (((W . beta_line') = I1) and ((W . beta_line) = I0) and (((W . MASK_2) = I1) or (not ((W . beta_line) = I0)) or ((W . MASK_0) = I1) or ((W . MASK_1) = I1)) and (((W . MASK_2) = I1) or ((W . MASK_0) = I1) or ((W . MASK_1) = I1))) or (((not ((W . beta_line) = I0)) or (((W . MASK_2) = I0) and ((W . MASK_0) = I0) and ((W . MASK_1) = I0))) and ((not ((W . trigger_beta) = T)) or (not ((W . beta_line) = I1))) and (((W . MASK_2) = I1) or (not ((W . beta_line) = I0)) or ((W . MASK_0) = I1) or ((W . MASK_1) = I1)) and ((W . beta_line') = I6) and ((W . beta_line) = I5) and ((not ((W . beta_line) = I1)) or (not (not ((W . trigger_beta) = T))))) or (((not ((W . beta_line) = I0)) or (((W . MASK_2) = I0) and ((W . MASK_0) = I0) and ((W . MASK_1) = I0))) and ((not ((W . trigger_beta) = T)) or (not ((W . beta_line) = I1))) and (((W . MASK_2) = I1) or (not ((W . beta_line) = I0)) or ((W . MASK_0) = I1) or ((W . MASK_1) = I1)) and ((W . beta_line) = I2) and ((W . beta_line') = I3) and ((not ((W . beta_line) = I1)) or (not (not ((W . trigger_beta) = T))))) or (((not ((W . beta_line) = I0)) or (((W . MASK_2) = I0) and ((W . MASK_0) = I0) and ((W . MASK_1) = I0))) and ((not ((W . trigger_beta) = T)) or (not ((W . beta_line) = I1))) and (((W . MASK_2) = I1) or (not ((W . beta_line) = I0)) or ((W . MASK_0) = I1) or ((W . MASK_1) = I1)) and ((W . beta_line') = I5) and ((W . beta_line) = I4) and ((not ((W . beta_line) = I1)) or (not (not ((W . trigger_beta) = T))))) or (((W . beta_line) = I0) and ((W . beta_line') = I0) and ((W . MASK_2) = I0) and ((W . MASK_0) = I0) and ((W . MASK_1) = I0)) or (((not ((W . beta_line) = I0)) or (((W . MASK_2) = I0) and ((W . MASK_0) = I0) and ((W . MASK_1) = I0))) and ((W . beta_line) = I1) and (((W . MASK_2) = I1) or (not ((W . beta_line) = I0)) or ((W . MASK_0) = I1) or ((W . MASK_1) = I1)) and ((W . beta_line') = I2) and ((W . trigger_beta) = T) and ((not ((W . beta_line) = I1)) or (not (not ((W . trigger_beta) = T)))))) and ((((((W . MASK_2) = I0) and ((W . MASK_0) = I0) and ((W . MASK_1) = I0)) or (not ((W . alpha_line) = I0))) and ((W . alpha_line') = I4) and ((not (not ((W . trigger_alpha) = T))) or (not ((W . alpha_line) = I1))) and ((not ((W . trigger_alpha) = T)) or (not ((W . alpha_line) = I1))) and (((W . MASK_2) = I1) or ((W . MASK_0) = I1) or ((W . MASK_1) = I1) or (not ((W . alpha_line) = I0))) and ((W . alpha_line) = I3)) or (((W . alpha_line') = I1) and ((W . alpha_line) = I0) and (((W . MASK_2) = I1) or ((W . MASK_0) = I1) or ((W . MASK_1) = I1)) and (((W . MASK_2) = I1) or ((W . MASK_0) = I1) or ((W . MASK_1) = I1) or (not ((W . alpha_line) = I0)))) or (((((W . MASK_2) = I0) and ((W . MASK_0) = I0) and ((W . MASK_1) = I0)) or (not ((W . alpha_line) = I0))) and ((W . alpha_line) = I1) and ((W . alpha_line') = I1) and (not ((W . trigger_alpha) = T)) and (((W . MASK_2) = I1) or ((W . MASK_0) = I1) or ((W . MASK_1) = I1) or (not ((W . alpha_line) = I0)))) or (((W . MASK_2) = I0) and ((W . MASK_0) = I0) and ((W . alpha_line) = I0) and ((W . MASK_1) = I0) and ((W . alpha_line') = I0)) or (((((W . MASK_2) = I0) and ((W . MASK_0) = I0) and ((W . MASK_1) = I0)) or (not ((W . alpha_line) = I0))) and ((W . alpha_line) = I1) and ((W . alpha_line') = I2) and ((W . trigger_alpha) = T) and ((not (not ((W . trigger_alpha) = T))) or (not ((W . alpha_line) = I1))) and (((W . MASK_2) = I1) or ((W . MASK_0) = I1) or ((W . MASK_1) = I1) or (not ((W . alpha_line) = I0)))) or (((((W . MASK_2) = I0) and ((W . MASK_0) = I0) and ((W . MASK_1) = I0)) or (not ((W . alpha_line) = I0))) and ((W . alpha_line') = I3) and ((W . alpha_line) = I2) and ((not (not ((W . trigger_alpha) = T))) or (not ((W . alpha_line) = I1))) and ((not ((W . trigger_alpha) = T)) or (not ((W . alpha_line) = I1))) and (((W . MASK_2) = I1) or ((W . MASK_0) = I1) or ((W . MASK_1) = I1) or (not ((W . alpha_line) = I0)))) or (((((W . MASK_2) = I0) and ((W . MASK_0) = I0) and ((W . MASK_1) = I0)) or (not ((W . alpha_line) = I0))) and ((W . alpha_line) = I5) and ((W . alpha_line') = I6) and ((not (not ((W . trigger_alpha) = T))) or (not ((W . alpha_line) = I1))) and ((not ((W . trigger_alpha) = T)) or (not ((W . alpha_line) = I1))) and (((W . MASK_2) = I1) or ((W . MASK_0) = I1) or ((W . MASK_1) = I1) or (not ((W . alpha_line) = I0)))) or (((((W . MASK_2) = I0) and ((W . MASK_0) = I0) and ((W . MASK_1) = I0)) or (not ((W . alpha_line) = I0))) and ((W . alpha_line') = I5) and ((not (not ((W . trigger_alpha) = T))) or (not ((W . alpha_line) = I1))) and ((W . alpha_line) = I4) and ((not ((W . trigger_alpha) = T)) or (not ((W . alpha_line) = I1))) and (((W . MASK_2) = I1) or ((W . MASK_0) = I1) or ((W . MASK_1) = I1) or (not ((W . alpha_line) = I0)))) or (((((W . MASK_2) = I0) and ((W . MASK_0) = I0) and ((W . MASK_1) = I0)) or (not ((W . alpha_line) = I0))) and ((W . alpha_line) = I6) and ((not (not ((W . trigger_alpha) = T))) or (not ((W . alpha_line) = I1))) and ((not ((W . trigger_alpha) = T)) or (not ((W . alpha_line) = I1))) and (((W . MASK_2) = I1) or ((W . MASK_0) = I1) or ((W . MASK_1) = I1) or (not ((W . alpha_line) = I0))) and ((W . alpha_line') = I0))) and ((((W . theta_line) = I3) and ((W . trigger_alpha') = T)) or (((not ((W . main_trigger) = I1)) or (not ((W . beta_line) = I5))) and (not ((W . theta_line) = I3)) and (not ((W . trigger_alpha') = T)) and ((W . alpha_line) = I3)) or (((not ((W . main_trigger) = I1)) or (not ((W . beta_line) = I5))) and ((W . trigger_alpha') in (W . trigger_alpha)) and (not ((W . alpha_line) = I3)) and (not ((W . theta_line) = I3))) or ((not ((W . theta_line) = I3)) and ((W . beta_line) = I5) and ((W . main_trigger) = I1) and ((W . trigger_alpha') = T))) and ((((W . MASK_0') = I1) and ((W . theta_line) = I6) and ((W . MASK_1) = I1)) or (((not ((W . theta_line) = I6)) or ((W . MASK_1) = I0)) and (((W . MASK_0) = I0) or (not ((W . theta_line) = I6))) and ((W . MASK_0') in (W . MASK_0))) or (((not ((W . theta_line) = I6)) or ((W . MASK_1) = I0)) and ((W . MASK_0') = I0) and ((W . MASK_0) = I1) and ((W . theta_line) = I6))) and ((((W . trigger_beta') = T) and ((W . theta_line) = I4)) or ((not ((W . theta_line) = I4)) and ((W . trigger_beta') in (W . trigger_beta)) and (not ((W . beta_line) = I3)) and ((not ((W . alpha_line) = I5)) or (not ((W . main_trigger) = I1)))) or ((not ((W . theta_line) = I4)) and ((not ((W . alpha_line) = I5)) or (not ((W . main_trigger) = I1))) and ((W . beta_line) = I3) and (not ((W . trigger_beta') = T))) or ((not ((W . theta_line) = I4)) and ((W . alpha_line) = I5) and ((W . trigger_beta') = T) and ((W . main_trigger) = I1))) and ((W . PIN_1') in (W . PIN_1)) and ((W . PIN_0') in (W . PIN_0)) and ((W . PIN_2') in (W . PIN_2)) and ((((W . MASK_2') in (W . MASK_2)) and (((W . MASK_2) = I0) or (not ((W . theta_line) = I6)))) or (((W . MASK_2) = I1) and ((W . MASK_2') = I0) and ((W . theta_line) = I6))) and ((((W . beta_line) = I2) and (((W . RESULT_0) = I0) or ((W . MASK_0) = I1)) and (((W . RESULT_0) = I1) or ((W . MASK_0) = I1) or (not ((W . alpha_line) = I2))) and (((W . RESULT_0) = I0) or ((W . MASK_0) = I1) or (not ((W . beta_line) = I2))) and ((W . RESULT_0') = I0) and ((((W . RESULT_0) = I0) and ((W . MASK_0) = I0)) or (not ((W . alpha_line) = I2)))) or (((W . beta_line) = I2) and ((W . RESULT_0') = I1) and ((W . RESULT_0) = I1) and (((W . RESULT_0) = I1) or ((W . MASK_0) = I1) or (not ((W . alpha_line) = I2))) and ((W . MASK_0) = I0) and ((((W . RESULT_0) = I0) and ((W . MASK_0) = I0)) or (not ((W . alpha_line) = I2)))) or ((((W . RESULT_0) = I1) or ((W . MASK_0) = I1) or (not ((W . alpha_line) = I2))) and (((W . RESULT_0) = I0) or ((W . MASK_0) = I1) or (not ((W . beta_line) = I2))) and ((W . RESULT_0') in (W . RESULT_0)) and ((((W . RESULT_0) = I1) and ((W . MASK_0) = I0)) or (not ((W . beta_line) = I2))) and ((((W . RESULT_0) = I0) and ((W . MASK_0) = I0)) or (not ((W . alpha_line) = I2)))) or (((W . RESULT_0) = I0) and ((W . MASK_0) = I0) and ((W . alpha_line) = I2) and ((W . RESULT_0') = I0) and ((((W . RESULT_0) = I0) and ((W . MASK_0) = I0)) or (not ((W . alpha_line) = I2)))) or (((W . RESULT_0') = I1) and (((W . RESULT_0) = I1) or ((W . MASK_0) = I1)) and ((W . alpha_line) = I2))) and ((((((W . RESULT_1) = I0) and ((W . MASK_1) = I0)) or (not ((W . alpha_line) = I2))) and (((W . RESULT_1) = I1) or ((W . MASK_1) = I1) or (not ((W . alpha_line) = I2))) and ((W . beta_line) = I2) and ((W . RESULT_1) = I1) and ((W . RESULT_1') = I1) and ((W . MASK_1) = I0)) or (((((W . RESULT_1) = I0) and ((W . MASK_1) = I0)) or (not ((W . alpha_line) = I2))) and (((W . RESULT_1) = I1) or ((W . MASK_1) = I1) or (not ((W . alpha_line) = I2))) and ((W . beta_line) = I2) and (((W . RESULT_1) = I0) or ((W . MASK_1) = I1)) and (((W . RESULT_1) = I0) or ((W . MASK_1) = I1) or (not ((W . beta_line) = I2))) and ((W . RESULT_1') = I0)) or ((((W . RESULT_1) = I1) or ((W . MASK_1) = I1)) and ((W . alpha_line) = I2) and ((W . RESULT_1') = I1)) or (((((W . RESULT_1) = I0) and ((W . MASK_1) = I0)) or (not ((W . alpha_line) = I2))) and ((W . RESULT_1) = I0) and ((W . alpha_line) = I2) and ((W . MASK_1) = I0) and ((W . RESULT_1') = I0)) or (((((W . RESULT_1) = I0) and ((W . MASK_1) = I0)) or (not ((W . alpha_line) = I2))) and ((((W . RESULT_1) = I1) and ((W . MASK_1) = I0)) or (not ((W . beta_line) = I2))) and (((W . RESULT_1) = I1) or ((W . MASK_1) = I1) or (not ((W . alpha_line) = I2))) and (((W . RESULT_1) = I0) or ((W . MASK_1) = I1) or (not ((W . beta_line) = I2))) and ((W . RESULT_1') in (W . RESULT_1)))))
  }
/* 
  State machine
  */
pred FSM[W : Main] {
  (define_halt[W]) and (init_0[W]) and (invar14[W]) and (range_MASK_0[W]) and (range_MASK_1[W]) and (range_MASK_2[W]) and (range_PIN_0[W]) and (range_PIN_1[W]) and (range_PIN_2[W]) and (range_RESULT_0[W]) and (range_RESULT_1[W]) and (range_RESULT_2[W]) and (range_alpha_line[W]) and (range_beta_line[W]) and (range_main_trigger[W]) and (range_theta_line[W]) and (trans0[W])
  }
/* 
  Auxiliary model definitions
  */