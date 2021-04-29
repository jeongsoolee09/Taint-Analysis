// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.plasma;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;
import org.bytedeco.arrow.*;
import static org.bytedeco.arrow.global.arrow.*;

import static org.bytedeco.arrow.global.plasma.*;
  // namespace plasma
@Name("std::hash<plasma::UniqueID>") @Properties(inherit = org.bytedeco.arrow.presets.plasma.class)
public class UniqueIDHash extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public UniqueIDHash() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public UniqueIDHash(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public UniqueIDHash(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public UniqueIDHash position(long position) {
        return (UniqueIDHash)super.position(position);
    }
    @Override public UniqueIDHash getPointer(long i) {
        return new UniqueIDHash((Pointer)this).position(position + i);
    }

  public native @Cast("std::size_t") @Name("operator ()") long apply(@Const @ByRef UniqueID id);
}