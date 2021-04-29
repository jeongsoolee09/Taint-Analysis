// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.systems.windows;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.systems.global.windows.*;


//
// Format of data for (F)XSAVE/(F)XRSTOR instruction
//

@Properties(inherit = org.bytedeco.systems.presets.windows.class)
public class XSAVE_FORMAT extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public XSAVE_FORMAT() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public XSAVE_FORMAT(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public XSAVE_FORMAT(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public XSAVE_FORMAT position(long position) {
        return (XSAVE_FORMAT)super.position(position);
    }
    @Override public XSAVE_FORMAT getPointer(long i) {
        return new XSAVE_FORMAT(this).position(position + i);
    }

    public native @Cast("WORD") short ControlWord(); public native XSAVE_FORMAT ControlWord(short setter);
    public native @Cast("WORD") short StatusWord(); public native XSAVE_FORMAT StatusWord(short setter);
    public native @Cast("BYTE") byte TagWord(); public native XSAVE_FORMAT TagWord(byte setter);
    public native @Cast("BYTE") byte Reserved1(); public native XSAVE_FORMAT Reserved1(byte setter);
    public native @Cast("WORD") short ErrorOpcode(); public native XSAVE_FORMAT ErrorOpcode(short setter);
    public native @Cast("DWORD") int ErrorOffset(); public native XSAVE_FORMAT ErrorOffset(int setter);
    public native @Cast("WORD") short ErrorSelector(); public native XSAVE_FORMAT ErrorSelector(short setter);
    public native @Cast("WORD") short Reserved2(); public native XSAVE_FORMAT Reserved2(short setter);
    public native @Cast("DWORD") int DataOffset(); public native XSAVE_FORMAT DataOffset(int setter);
    public native @Cast("WORD") short DataSelector(); public native XSAVE_FORMAT DataSelector(short setter);
    public native @Cast("WORD") short Reserved3(); public native XSAVE_FORMAT Reserved3(short setter);
    public native @Cast("DWORD") int MxCsr(); public native XSAVE_FORMAT MxCsr(int setter);
    public native @Cast("DWORD") int MxCsr_Mask(); public native XSAVE_FORMAT MxCsr_Mask(int setter);
    public native @ByRef M128A FloatRegisters(int i); public native XSAVE_FORMAT FloatRegisters(int i, M128A setter);
    @MemberGetter public native M128A FloatRegisters();

// #if defined(_WIN64)

    public native @ByRef M128A XmmRegisters(int i); public native XSAVE_FORMAT XmmRegisters(int i, M128A setter);
    @MemberGetter public native M128A XmmRegisters();
    public native @Cast("BYTE") byte Reserved4(int i); public native XSAVE_FORMAT Reserved4(int i, byte setter);
    @MemberGetter public native @Cast("BYTE*") BytePointer Reserved4();

// #else

// #endif

}
