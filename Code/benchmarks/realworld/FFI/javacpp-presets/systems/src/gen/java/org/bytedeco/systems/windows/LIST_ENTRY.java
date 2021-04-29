// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.systems.windows;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.systems.global.windows.*;
       
//
//  Doubly linked list structure.  Can be used as either a list head, or
//  as link words.
//

@Properties(inherit = org.bytedeco.systems.presets.windows.class)
public class LIST_ENTRY extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public LIST_ENTRY() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public LIST_ENTRY(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public LIST_ENTRY(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public LIST_ENTRY position(long position) {
        return (LIST_ENTRY)super.position(position);
    }
    @Override public LIST_ENTRY getPointer(long i) {
        return new LIST_ENTRY(this).position(position + i);
    }

   public native LIST_ENTRY Flink(); public native LIST_ENTRY Flink(LIST_ENTRY setter);
   public native LIST_ENTRY Blink(); public native LIST_ENTRY Blink(LIST_ENTRY setter);
}
