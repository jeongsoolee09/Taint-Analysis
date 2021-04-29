// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.systems.windows;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.systems.global.windows.*;
 // maximum number of exception parameters

//
// Exception record definition.
//

@Properties(inherit = org.bytedeco.systems.presets.windows.class)
public class EXCEPTION_RECORD extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public EXCEPTION_RECORD() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public EXCEPTION_RECORD(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public EXCEPTION_RECORD(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public EXCEPTION_RECORD position(long position) {
        return (EXCEPTION_RECORD)super.position(position);
    }
    @Override public EXCEPTION_RECORD getPointer(long i) {
        return new EXCEPTION_RECORD(this).position(position + i);
    }

    public native @Cast("DWORD") int ExceptionCode(); public native EXCEPTION_RECORD ExceptionCode(int setter);
    public native @Cast("DWORD") int ExceptionFlags(); public native EXCEPTION_RECORD ExceptionFlags(int setter);
    public native EXCEPTION_RECORD ExceptionRecord(); public native EXCEPTION_RECORD ExceptionRecord(EXCEPTION_RECORD setter);
    public native @Cast("PVOID") Pointer ExceptionAddress(); public native EXCEPTION_RECORD ExceptionAddress(Pointer setter);
    public native @Cast("DWORD") int NumberParameters(); public native EXCEPTION_RECORD NumberParameters(int setter);
    public native @Cast("ULONG_PTR") long ExceptionInformation(int i); public native EXCEPTION_RECORD ExceptionInformation(int i, long setter);
    @MemberGetter public native @Cast("ULONG_PTR*") SizeTPointer ExceptionInformation();
    }