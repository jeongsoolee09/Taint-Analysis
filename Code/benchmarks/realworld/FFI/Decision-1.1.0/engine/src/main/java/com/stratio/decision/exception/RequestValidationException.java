/**
 * Copyright (C) 2014 Stratio (http://stratio.com)
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *         http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package com.stratio.decision.exception;

public class RequestValidationException extends Exception {

    private static final long serialVersionUID = 1191962540939323833L;

    private final int code;

    public RequestValidationException(int code, String message, Throwable cause) {
        super(message, cause);
        this.code = code;
    }

    public RequestValidationException(int code, String message) {
        super(message);
        this.code = code;
    }

    public RequestValidationException(int code, Throwable cause) {
        super(cause);
        this.code = code;
    }

    public int getCode() {
        return code;
    }

    @Override
    public String getMessage() {
        if (super.getMessage() == null) {
            return this.getCause().getMessage();
        } else {
            return super.getMessage();
        }
    }
}
