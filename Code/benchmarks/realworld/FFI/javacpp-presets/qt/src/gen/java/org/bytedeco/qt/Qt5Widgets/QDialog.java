// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.qt.Qt5Widgets;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;
import org.bytedeco.qt.Qt5Core.*;
import static org.bytedeco.qt.global.Qt5Core.*;
import org.bytedeco.qt.Qt5Gui.*;
import static org.bytedeco.qt.global.Qt5Gui.*;

import static org.bytedeco.qt.global.Qt5Widgets.*;

// Parsed from QtWidgets/qdialog.h

@Properties(inherit = org.bytedeco.qt.presets.Qt5Widgets.class)
public class QDialog extends QWidget {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public QDialog(Pointer p) { super(p); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public QDialog(long size) { super((Pointer)null); allocateArray(size); }
    private native void allocateArray(long size);
    @Override public QDialog position(long position) {
        return (QDialog)super.position(position);
    }
    @Override public QDialog getPointer(long i) {
        return new QDialog(this).position(position + i);
    }

    public QDialog(QWidget parent/*=nullptr*/, @ByVal(nullValue = "Qt::WindowFlags()") @Cast("Qt::WindowFlags") int f) { super((Pointer)null); allocate(parent, f); }
    private native void allocate(QWidget parent/*=nullptr*/, @ByVal(nullValue = "Qt::WindowFlags()") @Cast("Qt::WindowFlags") int f);
    public QDialog() { super((Pointer)null); allocate(); }
    private native void allocate();

    /** enum QDialog::DialogCode */
    public static final int Rejected = 0, Accepted = 1;

    public native int result();

    @Virtual public native void setVisible(@Cast("bool") boolean visible);

// #if QT_DEPRECATED_SINCE(5, 13)
// #endif

    public native @ByVal QSize sizeHint();
    public native @ByVal QSize minimumSizeHint();

    public native void setSizeGripEnabled(@Cast("bool") boolean arg0);
    public native @Cast("bool") boolean isSizeGripEnabled();

    public native void setModal(@Cast("bool") boolean modal);
    public native void setResult(int r);
    @Virtual public native void open();
    @Virtual public native int exec();
    @Virtual public native void done(int arg0);
    @Virtual public native void accept();
    @Virtual public native void reject();
    @Virtual protected native void closeEvent(QCloseEvent arg0);
    @Virtual protected native @Cast("bool") boolean eventFilter(QObject arg0, QEvent arg1);
}