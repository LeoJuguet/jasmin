regs = {}
regs["RAX"] = {8: "%al", 16: "%ax", 32 : "%eax", 64 : "%rax"}
regs["RCX"] = {8: "%cl", 16: "%cx", 32 : "%ecx", 64 : "%rcx"}
regs["RDX"] = {8: "%dl", 16: "%dx", 32 : "%edx", 64 : "%rdx"}
regs["RBX"] = {8: "%bl", 16: "%bx", 32 : "%ebx", 64 : "%rbx"}
regs["RSP"] = {8: "%spl", 16: "%sp", 32 : "%esp", 64 : "%rsp"}
regs["RBP"] = {8: "%bpl", 16: "%bp", 32 : "%ebp", 64 : "%rbp"}
regs["RSI"] = {8: "%sil", 16: "%si", 32 : "%esi", 64 : "%rsi"}
regs["RDI"] = {8: "%dil", 16: "%di", 32 : "%edi", 64 : "%rdi"}
regs["R8"]  = {8: "%r8b", 16: "%r8w", 32 : "%r8d", 64 : "%r8"}
regs["R9"]  = {8: "%r9b", 16: "%r9w", 32 : "%r9d", 64 : "%r9"}
regs["R10"] = {8: "%r10b", 16: "%r10w", 32 : "%r10d", 64 : "%r10"}
regs["R11"] = {8: "%r11b", 16: "%r11w", 32 : "%r11d", 64 : "%r11"}
regs["R12"] = {8: "%r12b", 16: "%r12w", 32 : "%r12d", 64 : "%r12"}
regs["R13"] = {8: "%r13b", 16: "%r13w", 32 : "%r13d", 64 : "%r13"}
regs["R14"] = {8: "%r14b", 16: "%r14w", 32 : "%r14d", 64 : "%r14"}
regs["R15"] = {8: "%r15b", 16: "%r15w", 32 : "%r15d", 64 : "%r15"}

xregs = {}
xregs["XMM0"] = {128: "%xmm0", 256 : "%ymm0"}
xregs["XMM1"] = {128: "%xmm1", 256 : "%ymm1"}
xregs["XMM2"] = {128: "%xmm2", 256 : "%ymm2"}
xregs["XMM3"] = {128: "%xmm3", 256 : "%ymm3"}
xregs["XMM4"] = {128: "%xmm4", 256 : "%ymm4"}
xregs["XMM5"] = {128: "%xmm5", 256 : "%ymm5"}
xregs["XMM6"] = {128: "%xmm6", 256 : "%ymm6"}
xregs["XMM7"] = {128: "%xmm7", 256 : "%ymm7"}
xregs["XMM8"] = {128: "%xmm8", 256 : "%ymm8"}
xregs["XMM9"] = {128: "%xmm9", 256 : "%ymm9"}
xregs["XMM10"] = {128: "%xmm10", 256 : "%ymm10"}
xregs["XMM11"] = {128: "%xmm11", 256 : "%ymm11"}
xregs["XMM12"] = {128: "%xmm12", 256 : "%ymm12"}
xregs["XMM13"] = {128: "%xmm13", 256 : "%ymm13"}
xregs["XMM14"] = {128: "%xmm14", 256 : "%ymm14"}
xregs["XMM15"] = {128: "%xmm15", 256 : "%ymm15"}

x86_conds           = {}
x86_conds["O_ct"]   = "o"
x86_conds["NO_ct"]  = "no"
x86_conds["B_ct"]   = "b"
x86_conds["NB_ct"]  = "nb"
x86_conds["E_ct"]   = "e"
x86_conds["NE_ct"]  = "ne"
x86_conds["BE_ct"]  = "be"
x86_conds["NBE_ct"] = "nbe"
x86_conds["S_ct"]   = "s"
x86_conds["NS_ct"]  = "ns"
x86_conds["P_ct"]   = "p"
x86_conds["NP_ct"]  = "np"
x86_conds["L_ct"]   = "l"
x86_conds["NL_ct"]  = "nl"
x86_conds["LE_ct"]  = "le"
x86_conds["NLE_ct"] = "nle"

ops_zero_arg            = {}
ops_zero_arg["CQO"]     = "cqo"
ops_zero_arg["LFENCE"]  = "lfence"
ops_zero_arg["MFENCE"]  = "mfence"
ops_zero_arg["SFENCE"]  = "sfence"
ops_zero_arg["CLC"]     = "clc"
ops_zero_arg["STC"]     = "stc"

ops_one_arg             = {}
ops_one_arg["NEG"]      = "neg"
ops_one_arg["INC"]      = "inc"
ops_one_arg["DEC"]      = "dec"
ops_one_arg["MUL"]      = "mul"
ops_one_arg["DIV"]      = "div"
ops_one_arg["IMUL"]     = "imul"
ops_one_arg["IDIV"]     = "idiv"
ops_one_arg["NOT"]      = "not"
ops_one_arg["BSWAP"]    = "bswap"

ops_two_args            = {}
ops_two_args["ADD"]     = "add"
ops_two_args["ADC"]     = "adc"
ops_two_args["ADCX"]    = "adcx"
ops_two_args["ADOX"]    = "adox"
ops_two_args["BT"]      = "bt"
ops_two_args["SUB"]     = "sub"
ops_two_args["SBB"]     = "sbb"
ops_two_args["IMULr"]   = "imul"
ops_two_args["LZCNT"]   = "lzcnt"
ops_two_args["AND"]     = "and"
ops_two_args["OR"]      = "or"
ops_two_args["XOR"]     = "xor"
ops_two_args["POPCNT"]  = "popcnt"
ops_two_args["CMP"]     = "cmp"
ops_two_args["TEST"]    = "test"
ops_two_args["MOV"]     = "mov"

ops_two_args_two_sizes = {}
ops_two_args_two_sizes["MOVSX"]   = "movs"
ops_two_args_two_sizes["MOVZX"]   = "movz"

ops_three_args                  = {}
ops_three_args["ANDN"]          = "andn"
ops_three_args["PEXT"]          = "pext"
ops_three_args["PDEP"]          = "pdep"
ops_three_args["MULX_lo_hi"]    = "mulx"

ops_one_arg_imm8 = {}
ops_one_arg_imm8["RCL"] = "rcl"
ops_one_arg_imm8["RCR"] = "rcr"
ops_one_arg_imm8["ROL"] = "rol"
ops_one_arg_imm8["ROR"] = "ror"
ops_one_arg_imm8["SAL"] = "sal"
ops_one_arg_imm8["SAR"] = "sar"
ops_one_arg_imm8["SHL"] = "shl"
ops_one_arg_imm8["SHR"] = "shr"

ops_two_arg_imm8 = {}
ops_two_arg_imm8["SHLD"] = "shld"
ops_two_arg_imm8["SHRD"] = "shrd"

ops_two_args_vec                    = {}
ops_two_args_vec["VPTEST"]          = "vptest"

ops_three_args_vec                  = {}
ops_three_args_vec["VPAND"]         = "vpand"
ops_three_args_vec["VPANDN"]        = "vpandn"
ops_three_args_vec["VPOR"]          = "vpor"
ops_three_args_vec["VPXOR"]         = "vpxor"
ops_three_args_vec["VPMUL"]         = "vpmuldq"
ops_three_args_vec["VPMULU"]        = "vpmuludq"
ops_three_args_vec["VPSHUFB"]       = "vpshufb"
ops_three_args_vec["VPMADDUBSW"]    = "vpmaddubsw"
ops_three_args_vec["VPMADDWD"]      = "vpmaddwd"

# TODO: automate this size variation later
ops_three_args_vec128_size                  = {}
ops_three_args_vec128_size["VPMULL_8u16"]   = "vpmullw"
ops_three_args_vec128_size["VPMULH_8u16"]   = "vpmulhw"
ops_three_args_vec128_size["VPMULHU_8u16"]  = "vpmulhuw"
ops_three_args_vec128_size["VPMULHRS_8u16"] = "vpmulhrsw"

ops_three_args_vec128_size["VPACKUS_8u16"]  = "vpackuswb"
ops_three_args_vec128_size["VPACKUS_4u32"]  = "vpackusdw"

ops_three_args_vec128_size["VPACKSS_8u16"]  = "vpacksswb"
ops_three_args_vec128_size["VPACKSS_4u32"]  = "vpackssdw"

ops_three_args_vec128_size["VPUNPCKH_16u8"] = "vpunpckhbw"
ops_three_args_vec128_size["VPUNPCKH_8u16"] = "vpunpckhwd"
ops_three_args_vec128_size["VPUNPCKH_4u32"] = "vpunpckhdq"
ops_three_args_vec128_size["VPUNPCKH_2u64"] = "vpunpckhqdq"

ops_three_args_vec128_size["VPUNPCKL_16u8"] = "vpunpcklbw"
ops_three_args_vec128_size["VPUNPCKL_8u16"] = "vpunpcklwd"
ops_three_args_vec128_size["VPUNPCKL_4u32"] = "vpunpckldq"
ops_three_args_vec128_size["VPUNPCKL_2u64"] = "vpunpcklqdq"

ops_three_args_vec128_size["VPMINU_16u8"]   = "vpminub"
ops_three_args_vec128_size["VPMINU_8u16"]   = "vpminuw"
ops_three_args_vec128_size["VPMINU_4u32"]   = "vpminud"

ops_three_args_vec128_size["VPMINS_16u8"]   = "vpminsb"
ops_three_args_vec128_size["VPMINS_8u16"]   = "vpminsw"
ops_three_args_vec128_size["VPMINS_4u32"]   = "vpminsd"

ops_three_args_vec128_size["VPMAXU_16u8"]   = "vpmaxub"
ops_three_args_vec128_size["VPMAXU_8u16"]   = "vpmaxuw"
ops_three_args_vec128_size["VPMAXU_4u32"]   = "vpmaxud"

ops_three_args_vec128_size["VPMAXS_16u8"]   = "vpmaxsb"
ops_three_args_vec128_size["VPMAXS_8u16"]   = "vpmaxsw"
ops_three_args_vec128_size["VPMAXS_4u32"]   = "vpmaxsd"

ops_three_args_vec128_size["VPADD_16u8"]    = "vpaddb"
ops_three_args_vec128_size["VPADD_8u16"]    = "vpaddw"
ops_three_args_vec128_size["VPADD_4u32"]    = "vpaddd"
ops_three_args_vec128_size["VPADD_2u64"]    = "vpaddq"

ops_three_args_vec128_size["VPSUB_16u8"]    = "vpsubb"
ops_three_args_vec128_size["VPSUB_8u16"]    = "vpsubw"
ops_three_args_vec128_size["VPSUB_4u32"]    = "vpsubd"
ops_three_args_vec128_size["VPSUB_2u64"]    = "vpsubq"

ops_three_args_vec128_size["VPAVG_16u8"]    = "vpavgb"
ops_three_args_vec128_size["VPAVG_8u16"]    = "vpavgw"
ops_three_args_vec128_size["VPAVG_4u32"]    = "vpavgd"
ops_three_args_vec128_size["VPAVG_2u64"]    = "vpavgq"

ops_three_args_vec128_size["VPSLLV_8u16"]    = "vpsllvw"
ops_three_args_vec128_size["VPSLLV_4u32"]    = "vpsllvd"
ops_three_args_vec128_size["VPSLLV_2u64"]    = "vpsllvq"

ops_three_args_vec128_size["VPSRLV_8u16"]    = "vpsrlvw"
ops_three_args_vec128_size["VPSRLV_4u32"]    = "vpsrlvd"
ops_three_args_vec128_size["VPSRLV_2u64"]    = "vpsrlvq"

ops_three_args_vec128_size["VPCMPEQ_16u8"]      = "vpcmpeqb"
ops_three_args_vec128_size["VPCMPEQ_8u16"]      = "vpcmpeqw"
ops_three_args_vec128_size["VPCMPEQ_4u32"]      = "vpcmpeqd"
ops_three_args_vec128_size["VPCMPEQ_2u64"]      = "vpcmpeqq"

ops_three_args_vec128_size["VPCMPGT_16u8"]      = "vpcmpgtb"
ops_three_args_vec128_size["VPCMPGT_8u16"]      = "vpcmpgtw"
ops_three_args_vec128_size["VPCMPGT_4u32"]      = "vpcmpgtd"
ops_three_args_vec128_size["VPCMPGT_2u64"]      = "vpcmpgtq"

size_variations     = {}
size_variations[8]  = ["8", "b"]
size_variations[16] = ["16", "w"]
size_variations[32] = ["32", "l"]
size_variations[64] = ["64", "q"]
