// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.tesseract;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;
import org.bytedeco.leptonica.*;
import static org.bytedeco.leptonica.global.lept.*;

import static org.bytedeco.tesseract.global.tesseract.*;


@Name("TessCallback1<int>") @Properties(inherit = org.bytedeco.tesseract.presets.tesseract.class)
public class IntClearCallback extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public IntClearCallback() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public IntClearCallback(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public IntClearCallback(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public IntClearCallback position(long position) {
        return (IntClearCallback)super.position(position);
    }
    @Override public IntClearCallback getPointer(long i) {
        return new IntClearCallback(this).position(position + i);
    }

  @Virtual(true) public native void Run(int arg0);
}