// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.flycapture.FlyCapture2;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.flycapture.global.FlyCapture2.*;



    /**
     * \defgroup ImageSaveStructures Image saving structures.
     *
     * These structures define various parameters used for saving images.
     */

    /*@{*/

    /** Options for saving PNG images. */
    @Namespace("FlyCapture2") @NoOffset @Properties(inherit = org.bytedeco.flycapture.presets.FlyCapture2.class)
public class PNGOption extends Pointer {
        static { Loader.load(); }
        /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
        public PNGOption(Pointer p) { super(p); }
        /** Native array allocator. Access with {@link Pointer#position(long)}. */
        public PNGOption(long size) { super((Pointer)null); allocateArray(size); }
        private native void allocateArray(long size);
        @Override public PNGOption position(long position) {
            return (PNGOption)super.position(position);
        }
        @Override public PNGOption getPointer(long i) {
            return new PNGOption(this).position(position + i);
        }
    
        /** Whether to save the PNG as interlaced. */
        public native @Cast("bool") boolean interlaced(); public native PNGOption interlaced(boolean setter);
        /** Compression level (0-9). 0 is no compression, 9 is best compression. */
        public native @Cast("unsigned int") int compressionLevel(); public native PNGOption compressionLevel(int setter);
        /** Reserved for future use. */
        public native @Cast("unsigned int") int reserved(int i); public native PNGOption reserved(int i, int setter);
        @MemberGetter public native @Cast("unsigned int*") IntPointer reserved();

        public PNGOption() { super((Pointer)null); allocate(); }
        private native void allocate();
    }