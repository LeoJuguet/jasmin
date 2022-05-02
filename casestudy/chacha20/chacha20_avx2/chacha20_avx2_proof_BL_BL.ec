from Jasmin require import JModel Leakage_models.
require import AllCore IntDiv CoreMap List Chacha20_avx2_ct.

clone import Chacha20_avx2_ct.T with theory LeakageModel <-  LeakageModelBL.

equiv chacha20_avx2_ct : M.chacha20_avx2 ~ M.chacha20_avx2 : ={output, plain, len, nonce, key, M.leakages} ==> ={M.leakages}.
proof. proc;inline *;sim => />. qed.