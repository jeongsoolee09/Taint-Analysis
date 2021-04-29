// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.systems.windows;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.systems.global.windows.*;


@Properties(inherit = org.bytedeco.systems.presets.windows.class)
public class REASON_CONTEXT extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public REASON_CONTEXT() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public REASON_CONTEXT(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public REASON_CONTEXT(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public REASON_CONTEXT position(long position) {
        return (REASON_CONTEXT)super.position(position);
    }
    @Override public REASON_CONTEXT getPointer(long i) {
        return new REASON_CONTEXT(this).position(position + i);
    }

    public native @Cast("ULONG") long Version(); public native REASON_CONTEXT Version(long setter);
    public native @Cast("DWORD") int Flags(); public native REASON_CONTEXT Flags(int setter);
            @Name("Reason.Detailed.LocalizedReasonModule") public native @Cast("HMODULE") Pointer Reason_Detailed_LocalizedReasonModule(); public native REASON_CONTEXT Reason_Detailed_LocalizedReasonModule(Pointer setter);
            @Name("Reason.Detailed.LocalizedReasonId") public native @Cast("ULONG") long Reason_Detailed_LocalizedReasonId(); public native REASON_CONTEXT Reason_Detailed_LocalizedReasonId(long setter);
            @Name("Reason.Detailed.ReasonStringCount") public native @Cast("ULONG") long Reason_Detailed_ReasonStringCount(); public native REASON_CONTEXT Reason_Detailed_ReasonStringCount(long setter);
            @Name("Reason.Detailed.ReasonStrings") public native @Cast("LPWSTR*") PointerPointer Reason_Detailed_ReasonStrings(); public native REASON_CONTEXT Reason_Detailed_ReasonStrings(PointerPointer setter);

        @Name("Reason.SimpleReasonString") public native @Cast("LPWSTR") CharPointer Reason_SimpleReasonString(); public native REASON_CONTEXT Reason_SimpleReasonString(CharPointer setter);
}