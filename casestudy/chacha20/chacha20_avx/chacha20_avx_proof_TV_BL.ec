require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.
require import Leakage_models.
require Chacha20_avx_TV_BL.
import StdOrder.IntOrder Ring.IntID.

clone import Chacha20_avx_TV_BL.T with
theory LeakageModel <-  LeakageModelTV.

equiv chacha20_avx_ct :
  M.chacha20_avx ~ M.chacha20_avx : ={output, plain, len, nonce, key, M.leakages} ==> ={M.leakages}.
proof. proc;inline *;sim => />. qed.