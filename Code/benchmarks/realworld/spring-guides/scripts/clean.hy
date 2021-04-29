(import os.path)
(import os)
(import subprocess)


(setv root (os.path.join "/Users" "jslee" "Taint-Analysis" "Code"
                         "benchmarks" "realworld" "spring-guides"))


(setv dirs (->> (os.listdir :path root)
                (filter (fn [x] (in "gs" x)))
                (list)))


(defn one-pass [directory]
  (os.chdir (os.path.join directory "complete"))
  (setv clean (.run subprocess ["gradle" "clean"]))
  {"clean-fail" clean.returncode})


(defmain []
  (setv clean-failed [])
  (os.system "JAVA_HOME=/Library/Java/JavaVirtualMachines/jdk1.8.0_202.jdk/Contents/Home") ; setjava8
  (os.chdir root)
  (for [directory dirs]
    (setv returncodes (one-pass directory))
    (when (get returncodes "clean-fail")
      (.append clean-failed directory))
    (os.chdir root))
  (print "clean-failed:" clean-failed))
