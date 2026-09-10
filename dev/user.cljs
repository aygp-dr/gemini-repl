(ns user
  "REPL helper. From `npx shadow-cljs cljs-repl repl`, evaluate
  (require 'user) to load the project and instrument every s/fdef'd fn so
  bad calls fail fast with explain-data. (.cljs, not .clj: shadow-cljs's
  JVM would auto-load a dev/user.clj on startup.)"
  (:require [clojure.spec.test.alpha :as stest]
            [gemini-repl.core]))

(stest/instrument)
