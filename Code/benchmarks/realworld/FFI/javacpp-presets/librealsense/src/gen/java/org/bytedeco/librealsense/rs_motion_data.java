// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.librealsense;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.librealsense.global.RealSense.*;


/** \brief Motion data from gyroscope and accelerometer from the microcontroller */
@Properties(inherit = org.bytedeco.librealsense.presets.RealSense.class)
public class rs_motion_data extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public rs_motion_data() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public rs_motion_data(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public rs_motion_data(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public rs_motion_data position(long position) {
        return (rs_motion_data)super.position(position);
    }
    @Override public rs_motion_data getPointer(long i) {
        return new rs_motion_data(this).position(position + i);
    }

    public native @ByRef rs_timestamp_data timestamp_data(); public native rs_motion_data timestamp_data(rs_timestamp_data setter); 
    /** Signaled by firmware in case of an error */
    public native @Cast("unsigned int") int is_valid(); public native rs_motion_data is_valid(int setter); 
    /** Three [x,y,z] axes; 16-bit data for gyroscope [rad/sec], 12-bit for accelerometer; 2's complement [m/sec^2]*/
    public native float axes(int i); public native rs_motion_data axes(int i, float setter);
    @MemberGetter public native FloatPointer axes();
}
