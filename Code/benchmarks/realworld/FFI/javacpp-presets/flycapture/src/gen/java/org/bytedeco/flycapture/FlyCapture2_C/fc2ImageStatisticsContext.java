// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.flycapture.FlyCapture2_C;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;
import org.bytedeco.flycapture.FlyCapture2.*;
import static org.bytedeco.flycapture.global.FlyCapture2.*;

import static org.bytedeco.flycapture.global.FlyCapture2_C.*;


    /**
     * A context referring to the ImageStatistics object.
     */
    @Namespace @Name("void") @Opaque @Properties(inherit = org.bytedeco.flycapture.presets.FlyCapture2_C.class)
public class fc2ImageStatisticsContext extends Pointer {
        /** Empty constructor. Calls {@code super((Pointer)null)}. */
        public fc2ImageStatisticsContext() { super((Pointer)null); }
        /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
        public fc2ImageStatisticsContext(Pointer p) { super(p); }
    }
