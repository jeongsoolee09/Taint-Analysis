// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.spinnaker.Spinnaker_C;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.spinnaker.global.Spinnaker_C.*;


/**
 * Handle for node functionality. Created by calling
 * spinNodeMapGetNode(). No need to release, clear, or destroy.
 */
@Namespace @Name("void") @Opaque @Properties(inherit = org.bytedeco.spinnaker.presets.Spinnaker_C.class)
public class spinNodeHandle extends Pointer {
    /** Empty constructor. Calls {@code super((Pointer)null)}. */
    public spinNodeHandle() { super((Pointer)null); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public spinNodeHandle(Pointer p) { super(p); }
}
