// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.hyperscan;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.hyperscan.global.hyperscan.*;


/**
 * A Hyperscan pattern database.
 *
 * Generated by one of the Hyperscan compiler functions:
 *  - \ref hs_compile()
 *  - \ref hs_compile_multi()
 *  - \ref hs_compile_ext_multi()
 */
@Opaque @Properties(inherit = org.bytedeco.hyperscan.presets.hyperscan.class)
public class hs_database_t extends Pointer {
    /** Empty constructor. Calls {@code super((Pointer)null)}. */
    public hs_database_t() { super((Pointer)null); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public hs_database_t(Pointer p) { super(p); }
}
