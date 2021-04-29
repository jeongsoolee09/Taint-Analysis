// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.onnx;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.onnx.global.onnx.*;

@Name("std::map<std::string,std::shared_ptr<onnx::optimization::Pass> >") @Properties(inherit = org.bytedeco.onnx.presets.onnx.class)
public class StringPassMap extends Pointer {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public StringPassMap(Pointer p) { super(p); }
    public StringPassMap()       { allocate();  }
    private native void allocate();
    public native @Name("operator =") @ByRef StringPassMap put(@ByRef StringPassMap x);

    public boolean empty() { return size() == 0; }
    public native long size();

    @Index public native @SharedPtr Pass get(@StdString BytePointer i);
    public native StringPassMap put(@StdString BytePointer i, Pass value);

    public native @ByVal Iterator begin();
    public native @ByVal Iterator end();
    @NoOffset @Name("iterator") public static class Iterator extends Pointer {
        public Iterator(Pointer p) { super(p); }
        public Iterator() { }

        public native @Name("operator ++") @ByRef Iterator increment();
        public native @Name("operator ==") boolean equals(@ByRef Iterator it);
        public native @Name("operator *().first") @MemberGetter @StdString BytePointer first();
        public native @Name("operator *().second") @MemberGetter @SharedPtr @Const Pass second();
    }
}

