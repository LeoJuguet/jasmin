from Jasmin require import JModel.
require import List Int IntDiv CoreMap Leakage_models Keccak1600_scalar_TV_BL.

clone import Keccak1600_scalar_TV_BL.T with theory LeakageModel <- LeakageModelTV. 

equiv ct: 
  M.__keccak1600_scalar ~ M.__keccak1600_scalar :
     ={inlen,s_outlen,M.leakages,rate,in_0,s_out,iotas} ==> ={M.leakages}.
proof. proc; inline *; sim. qed.