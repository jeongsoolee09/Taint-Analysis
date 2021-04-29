// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.flycapture.FlyCapture2;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.flycapture.global.FlyCapture2.*;


    /** Options for saving Bitmap image. */
    @Namespace("FlyCapture2") @NoOffset @Properties(inherit = org.bytedeco.flycapture.presets.FlyCapture2.class)
public class BMPOption extends Pointer {
        static { Loader.load(); }
        /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
        public BMPOption(Pointer p) { super(p); }
        /** Native array allocator. Access with {@link Pointer#position(long)}. */
        public BMPOption(long size) { super((Pointer)null); allocateArray(size); }
        private native void allocateArray(long size);
        @Override public BMPOption position(long position) {
            return (BMPOption)super.position(position);
        }
        @Override public BMPOption getPointer(long i) {
            return new BMPOption(this).position(position + i);
        }
    
        public native @Cast("bool") boolean indexedColor_8bit(); public native BMPOption indexedColor_8bit(boolean setter);
        /** Reserved for future use. */
        public native @Cast("unsigned int") int reserved(int i); public native BMPOption reserved(int i, int setter);
        @MemberGetter public native @Cast("unsigned int*") IntPointer reserved();

        public BMPOption() { super((Pointer)null); allocate(); }
        private native void allocate();
    }
