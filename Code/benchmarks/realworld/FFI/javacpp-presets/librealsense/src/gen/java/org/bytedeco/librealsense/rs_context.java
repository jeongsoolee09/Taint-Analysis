// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.librealsense;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.librealsense.global.RealSense.*;


@Properties(inherit = org.bytedeco.librealsense.presets.RealSense.class)
public class rs_context extends Pointer {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public rs_context(Pointer p) { super(p); }

    public native @Cast("size_t") long get_device_count();
    public native rs_device get_device(int index);
}
