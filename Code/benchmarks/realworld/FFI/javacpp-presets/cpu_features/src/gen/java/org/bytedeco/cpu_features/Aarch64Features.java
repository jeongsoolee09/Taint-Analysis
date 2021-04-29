// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.cpu_features;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.cpu_features.global.cpu_features.*;


@Namespace("cpu_features") @Properties(inherit = org.bytedeco.cpu_features.presets.cpu_features.class)
public class Aarch64Features extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public Aarch64Features() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public Aarch64Features(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public Aarch64Features(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public Aarch64Features position(long position) {
        return (Aarch64Features)super.position(position);
    }
    @Override public Aarch64Features getPointer(long i) {
        return new Aarch64Features(this).position(position + i);
    }

  public native @NoOffset int fp(); public native Aarch64Features fp(int setter);          // Floating-point.
  public native @NoOffset int asimd(); public native Aarch64Features asimd(int setter);       // Advanced SIMD.
  public native @NoOffset int evtstrm(); public native Aarch64Features evtstrm(int setter);     // Generic timer generated events.
  public native @NoOffset int aes(); public native Aarch64Features aes(int setter);         // Hardware-accelerated Advanced Encryption Standard.
  public native @NoOffset int pmull(); public native Aarch64Features pmull(int setter);       // Polynomial multiply long.
  public native @NoOffset int sha1(); public native Aarch64Features sha1(int setter);        // Hardware-accelerated SHA1.
  public native @NoOffset int sha2(); public native Aarch64Features sha2(int setter);        // Hardware-accelerated SHA2-256.
  public native @NoOffset int crc32(); public native Aarch64Features crc32(int setter);       // Hardware-accelerated CRC-32.
  public native @NoOffset int atomics(); public native Aarch64Features atomics(int setter);     // Armv8.1 atomic instructions.
  public native @NoOffset int fphp(); public native Aarch64Features fphp(int setter);        // Half-precision floating point support.
  public native @NoOffset int asimdhp(); public native Aarch64Features asimdhp(int setter);     // Advanced SIMD half-precision support.
  public native @NoOffset int cpuid(); public native Aarch64Features cpuid(int setter);       // Access to certain ID registers.
  public native @NoOffset int asimdrdm(); public native Aarch64Features asimdrdm(int setter);    // Rounding Double Multiply Accumulate/Subtract.
  public native @NoOffset int jscvt(); public native Aarch64Features jscvt(int setter);       // Support for JavaScript conversion.
  public native @NoOffset int fcma(); public native Aarch64Features fcma(int setter);        // Floating point complex numbers.
  public native @NoOffset int lrcpc(); public native Aarch64Features lrcpc(int setter);       // Support for weaker release consistency.
  public native @NoOffset int dcpop(); public native Aarch64Features dcpop(int setter);       // Data persistence writeback.
  public native @NoOffset int sha3(); public native Aarch64Features sha3(int setter);        // Hardware-accelerated SHA3.
  public native @NoOffset int sm3(); public native Aarch64Features sm3(int setter);         // Hardware-accelerated SM3.
  public native @NoOffset int sm4(); public native Aarch64Features sm4(int setter);         // Hardware-accelerated SM4.
  public native @NoOffset int asimddp(); public native Aarch64Features asimddp(int setter);     // Dot product instruction.
  public native @NoOffset int sha512(); public native Aarch64Features sha512(int setter);      // Hardware-accelerated SHA512.
  public native @NoOffset int sve(); public native Aarch64Features sve(int setter);         // Scalable Vector Extension.
  public native @NoOffset int asimdfhm(); public native Aarch64Features asimdfhm(int setter);    // Additional half-precision instructions.
  public native @NoOffset int dit(); public native Aarch64Features dit(int setter);         // Data independent timing.
  public native @NoOffset int uscat(); public native Aarch64Features uscat(int setter);       // Unaligned atomics support.
  public native @NoOffset int ilrcpc(); public native Aarch64Features ilrcpc(int setter);      // Additional support for weaker release consistency.
  public native @NoOffset int flagm(); public native Aarch64Features flagm(int setter);       // Flag manipulation instructions.
  public native @NoOffset int ssbs(); public native Aarch64Features ssbs(int setter);        // Speculative Store Bypass Safe PSTATE bit.
  public native @NoOffset int sb(); public native Aarch64Features sb(int setter);          // Speculation barrier.
  public native @NoOffset int paca(); public native Aarch64Features paca(int setter);        // Address authentication.
  public native @NoOffset int pacg(); public native Aarch64Features pacg(int setter);        // Generic authentication.
  public native @NoOffset int dcpodp(); public native Aarch64Features dcpodp(int setter);      // Data cache clean to point of persistence.
  public native @NoOffset int sve2(); public native Aarch64Features sve2(int setter);        // Scalable Vector Extension (version 2).
  public native @NoOffset int sveaes(); public native Aarch64Features sveaes(int setter);      // SVE AES instructions.
  public native @NoOffset int svepmull(); public native Aarch64Features svepmull(int setter);    // SVE polynomial multiply long instructions.
  public native @NoOffset int svebitperm(); public native Aarch64Features svebitperm(int setter);  // SVE bit permute instructions.
  public native @NoOffset int svesha3(); public native Aarch64Features svesha3(int setter);     // SVE SHA3 instructions.
  public native @NoOffset int svesm4(); public native Aarch64Features svesm4(int setter);      // SVE SM4 instructions.
  public native @NoOffset int flagm2(); public native Aarch64Features flagm2(int setter);      // Additional flag manipulation instructions.
  public native @NoOffset int frint(); public native Aarch64Features frint(int setter);       // Floating point to integer rounding.
  public native @NoOffset int svei8mm(); public native Aarch64Features svei8mm(int setter);     // SVE Int8 matrix multiplication instructions.
  public native @NoOffset int svef32mm(); public native Aarch64Features svef32mm(int setter);    // SVE FP32 matrix multiplication instruction.
  public native @NoOffset int svef64mm(); public native Aarch64Features svef64mm(int setter);    // SVE FP64 matrix multiplication instructions.
  public native @NoOffset int svebf16(); public native Aarch64Features svebf16(int setter);     // SVE BFloat16 instructions.
  public native @NoOffset int i8mm(); public native Aarch64Features i8mm(int setter);        // Int8 matrix multiplication instructions.
  public native @NoOffset int bf16(); public native Aarch64Features bf16(int setter);        // BFloat16 instructions.
  public native @NoOffset int dgh(); public native Aarch64Features dgh(int setter);         // Data Gathering Hint instruction.
  public native @NoOffset int rng(); public native Aarch64Features rng(int setter);         // True random number generator support.
  public native @NoOffset int bti(); public native Aarch64Features bti(int setter);         // Branch target identification.

  // Make sure to update Aarch64FeaturesEnum below if you add a field here.
}