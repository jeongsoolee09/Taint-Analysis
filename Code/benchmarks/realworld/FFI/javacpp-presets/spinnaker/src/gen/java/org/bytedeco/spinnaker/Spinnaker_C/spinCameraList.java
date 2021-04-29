// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.spinnaker.Spinnaker_C;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.spinnaker.global.Spinnaker_C.*;


/**
 * Handle for interface functionality. Created by calling
 * spinSystemGetCameras() or spinInterfaceGetCameras(), which require
 * a call to spinCameraListClear() to clear, or
 * spinCameraListCreateEmpty(), which requires a call to
 * spinCameraListDestroy() to destroy.
 */
@Namespace @Name("void") @Opaque @Properties(inherit = org.bytedeco.spinnaker.presets.Spinnaker_C.class)
public class spinCameraList extends Pointer {
    /** Empty constructor. Calls {@code super((Pointer)null)}. */
    public spinCameraList() { super((Pointer)null); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public spinCameraList(Pointer p) { super(p); }
}
