// This will be all sorts of broken, no doubt.
// But since doing this via K is even more broken, we have little choice

module PRELUDE
    /*@
        mpsad
    */  
    rule <regstate>... absoluteUnsignedDifference(A:MInt, B:MInt) => ite(ugtMInt(A, B), subMInt(A, B), subMInt(B, A)) ...</regstate>
    rule <regstate>... selectSliceMPSAD(DEST:MInt, Offset:MInt, High:Int, Low:Int) =>
        concatenateMInt(mi(8, 0), 
            extractMask(DEST, High -Int Low +Int 1, (uvalueMInt(Offset) *Int 32) +Int Low)) ...</regstate>

    /*@ 
        Incr/Dec RSP. Used for push/pop instructions.
    */  
    rule <k> decRSPInBytes(I:Int) => .  ...</k>
        <regstate> RSMap:Map => updateMap(
            RSMap, 
            "RSP" |-> subMInt({RSMap["RSP"]}:>MInt, mi(64, I)))
        </regstate>

    rule <k> incRSPInBytes(I:Int) => .  ...</k>
        <regstate> RSMap:Map => updateMap(
            RSMap, 
            "RSP" |-> addMInt({RSMap["RSP"]}:>MInt, mi(64, I))
        )
        </regstate>

    rule <regstate>...
        selectSlice(SRC1:MInt, Imm8:MInt, CheckBit:Int, Start1:Int, Start2:Int)
            => ite(
                eqMInt(mi(1, 0), extractMInt(Imm8, CheckBit, CheckBit +Int 1)),
                extractMInt(SRC1, Start1, Start1 +Int 64),
                extractMInt(SRC1, Start2, Start2 +Int 64)
            )
        ...</regstate>


    /*@
        shiftCountMask(MIsrc, N):
        if N == 64: return and(MIsrc, 0x3F)
        else return and(MIsrc, 0x1F)
    */
    rule <k>... shiftCountMask(MI:MInt, I:Int) => #ifMInt I ==Int 64
                                            #then andMInt(MI, mi(bitwidthMInt(MI), 63))
                                            #else andMInt(MI, mi(bitwidthMInt(MI), 31))
                                            #fi ...</k>

    rule <regstate>... convToRegKeys(R) =>  convToRegKeysHelper(convSubRegsToRegs(R)) ...</regstate>

    rule <regstate>... getParentValue(R:Register, RSMap) => getRegisterValue(convSubRegsToRegs(R), RSMap) ...</regstate>
    rule <regstate>... getRegisterValue(R:R8,  RSMap)  =>  extractMask({RSMap[convToRegKeys(R)]}:>MInt, 8, 0) ...</regstate>
    rule <regstate>... getRegisterValue(R:R16, RSMap)  =>  extractMask({RSMap[convToRegKeys(R)]}:>MInt, 16, 0) ...</regstate>
    rule <regstate>... getRegisterValue(R:R32, RSMap)  =>  extractMask({RSMap[convToRegKeys(R)]}:>MInt, 32, 0) ...</regstate>
    rule <regstate>... getRegisterValue(R:R64, RSMap)  =>  {RSMap[convToRegKeys(R)]}:>MInt ...</regstate>
    rule <regstate>... getRegisterValue(R:Rh,  RSMap)  =>  extractMask({RSMap[convToRegKeys(R)]}:>MInt, 8, 8) ...</regstate>
    rule <regstate>... getRegisterValue(X:Xmm, RSMap)  =>  extractMask({RSMap[convToRegKeys(X)]}:>MInt, 128, 0) ...</regstate>
    rule <regstate>... getRegisterValue(Y:Ymm, RSMap)  =>  {RSMap[convToRegKeys(Y)]}:>MInt ...</regstate>

    rule <k>... getRegisterValue(R:R8,  RSMap)  =>  extractMask({RSMap[convToRegKeys(R)]}:>MInt, 8, 0) ...</k>
    rule <k>... getRegisterValue(R:R16, RSMap)  =>  extractMask({RSMap[convToRegKeys(R)]}:>MInt, 16, 0) ...</k>
    rule <k>... getRegisterValue(R:R32, RSMap)  =>  extractMask({RSMap[convToRegKeys(R)]}:>MInt, 32, 0) ...</k>
    rule <k>... getRegisterValue(R:R64, RSMap)  =>  {RSMap[convToRegKeys(R)]}:>MInt ...</k>
    rule <k>... getRegisterValue(R:Rh,  RSMap)  =>  extractMask({RSMap[convToRegKeys(R)]}:>MInt, 8, 8) ...</k>
    rule <k>... getRegisterValue(X:Xmm, RSMap)  =>  extractMask({RSMap[convToRegKeys(X)]}:>MInt, 128, 0) ...</k>
    rule <k>... getRegisterValue(Y:Ymm, RSMap)  =>  {RSMap[convToRegKeys(Y)]}:>MInt ...</k>

    rule <regstate>... getFlag(FName, RSMap) => {RSMap[FName]}:>MInt ...</regstate>

    rule <k> ... loadFromMemory(offset, size) => memLoadValue(z3_mem(offset, size)) ...</k>
    rule <regstate> ... loadFromMemory(offset, size) => memLoadValue(z3_mem(offset, size)) ...</regstate>

    /*@
        Set the registers values.
        
        setRegisterValue(MI, R:RW)
        Updates W bits of `underlying Register`.
        
        Assumption: bitwidthMInt(MI) == W
        Need to zeroExtend or signExtend if bitwidthMInt(MI) < W

        If bitwidthMInt(MI) > W, then more bits than W in `underlying register`
        will be clobbered.
        If bitwidthMInt(MI) < W, then lesser bits than W in `underlying register`
        will be clobbered.

        Ex. setRegisterValue(M8, %ah): Updates 8 bits in rax
        starting from lsb 8.
    */
    rule <k> setRegisterValue(memLoadValue( MI:MInt ):MemLoadValue, R:Register) => setRegisterValue(MI, R)  ...</k>

    rule <k> setRegisterValue(MI64:MInt, R:R64) => .  ...</k>
        <regstate>RSMap => updateMap(RSMap, convToRegKeys(R) |-> MI64)</regstate>

    rule <k> setRegisterValue(MI32:MInt, R:R32) => .  ...</k>
        <regstate>RSMap => updateMap(RSMap, convToRegKeys(R) |-> plugInMask(getRegisterValue(convSubRegsToRegs(R), RSMap),  MI32,  0))</regstate>

    rule <k> setRegisterValue(MI16:MInt, R:R16) => .  ...</k>
        <regstate>RSMap => updateMap(RSMap, convToRegKeys(R) |-> plugInMask(getRegisterValue(convSubRegsToRegs(R), RSMap),  MI16,  0))</regstate>

    rule <k> setRegisterValue(MI8:MInt, R:R8) => .  ...</k>
        <regstate>RSMap => updateMap(RSMap, convToRegKeys(R) |-> plugInMask(getRegisterValue(convSubRegsToRegs(R), RSMap),  MI8,   0))</regstate>

    rule <k> setRegisterValue(MI8:MInt, R:Rh) => .  ...</k>
        <regstate>RSMap => updateMap(RSMap, convToRegKeys(R) |-> plugInMask(getRegisterValue(convSubRegsToRegs(R), RSMap),  MI8,   8))</regstate>

    rule <k> setRegisterValue(MI128:MInt, X:Xmm) => .  ...</k>
        <regstate>RSMap => updateMap(RSMap, convToRegKeys(X) |-> plugInMask(getRegisterValue(convSubRegsToRegs(X), RSMap), MI128, 0))</regstate>

    rule <k> setRegisterValue(MI256:MInt, Y:Ymm) => .  ...</k>
        <regstate>RSMap => updateMap(RSMap, convToRegKeys(Y) |-> MI256)</regstate>

    rule <k> updateSignFlag(MI:MInt) => .  ...</k>
        <regstate>RSMap => updateMap(RSMap, "SF" |-> #ifMInt (sltMInt(MI, mi(bitwidthMInt(MI), 0))) #then mi(1, 1) #else mi(1, 0) #fi)</regstate>

    rule <k> updateZeroFlag(MI:MInt) => .  ...</k>
        <regstate>RSMap => updateMap(RSMap, "ZF" |-> #ifMInt (eqMInt(MI, mi(bitwidthMInt(MI), 0))) #then mi(1, 1) #else mi(1, 0) #fi)</regstate>

    rule <k> updateParityFlag(MI:MInt) => .  ...</k>
        <regstate>RSMap => updateMap(RSMap, "PF" |-> xorMInt(
                extractMInt(mi(64, popCount(extractMask(MI, 8, 0))), 63, 64),
                mi(1, 1)
            )
        )</regstate>


    /*@
        Setting the flags with 0 or 1.
    */
    rule 
    <k> setFlag(MI, FL) => . ...</k>
    <regstate>  
        RMap => updateMap(RMap, FL |-> MI)
    </regstate>

    rule <regstate>... extractMask(MI, NUM, P) => extractMInt(MI, bitwidthMInt(MI) -Int P -Int NUM, bitwidthMInt(MI) -Int P) ...</regstate>
    rule <k>... extractMask(MI, NUM, P) => extractMInt(MI, bitwidthMInt(MI) -Int P -Int NUM, bitwidthMInt(MI) -Int P) ...</k>
    
    rule <regstate>... handleImmediateWithSignExtend(I:Imm, M:Int, N:Int) => signExtend(mi(M,I), N) ...</regstate>

    rule <k> storeToMemory(val, offset, size) => . ...</k>
        <regstate>RSMap:Map => updateMap(RSMap,
            z3_mem(offset, size) |-> val
        )</regstate>

    rule <k> setParentValue(memLoadValue( MI:MInt ):MemLoadValue, R:Register) => 
        setRegisterValue(memLoadValue( MI:MInt ):MemLoadValue, convSubRegsToRegs(R))                                                    
    ...</k>
    rule <k> setParentValue(MI:MInt, R:Register) => 
        setRegisterValue(MI, convSubRegsToRegs(R))    
    ...</k>

    rule <k>
        parallelBitDeposit64(Mask:MInt, TempR:Register, DestR:Register, M:Int, K:Int) => 
        .
    ...</k>  
        <regstate> RSMap:Map => updateMap(RSMap, convToRegKeys(DestR) |-> __pdep64(Mask, __lookup(RSMap, convToRegKeys(TempR)))) </regstate>

    rule <k>
        parallelBitDeposit32(Mask:MInt, TempR:Register, DestR:Register, M:Int, K:Int) => 
        .
    ...</k>  
        <regstate> RSMap:Map => updateMap(RSMap, convToRegKeys(DestR) |-> __pdep32(Mask, __lookup(RSMap, convToRegKeys(TempR)))) </regstate>

    rule <k>
        parallelBitExtract64(Mask:MInt, TempR:Register, DestR:Register, M:Int, K:Int) => 
        .
    ...</k>  
        <regstate> RSMap:Map => updateMap(RSMap, convToRegKeys(DestR) |-> __pextr64(Mask, __lookup(RSMap, convToRegKeys(TempR)))) </regstate>

    rule <k>
        parallelBitExtract32(Mask:MInt, TempR:Register, DestR:Register, M:Int, K:Int) => 
        .
    ...</k>  
        <regstate> RSMap:Map => updateMap(RSMap, convToRegKeys(DestR) |-> __pextr32(Mask, __lookup(RSMap, convToRegKeys(TempR)))) </regstate>



    rule <regstate>... bitwidthMInt(extractMInt(:_, lo, hi)) => hi -Int lo ...</regstate>
    rule <regstate>... bitwidthMInt(z3_bitvec(:_, width)) => width ...</regstate>
    rule <regstate>... bitwidthMInt(z3_mem(:_, width)) => width ...</regstate>
    rule <regstate>... updateMap(map, key |-> newval) => key |-> newval, removeKey(map, key) ...</regstate>
    rule <regstate>... __sub_int(a, 0) => a ...</regstate>

    rule <regstate>... sameRegisters(R1:Register, R2:Register) => __sameRegisters(convToRegKeys(R1), convToRegKeys(R2)) ...</regstate>
    rule <k>... sameRegisters(R1:Register, R2:Register) => __sameRegisters(convToRegKeys(R1), convToRegKeys(R2)) ...</k>

    rule <regstate>... $ num => num ...</regstate>
endmodule