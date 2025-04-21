;;; This system is provided for convenience. Vendoring usually makes more sense.
(asdf:defsystem "semz.minisign-verify"
  :description "Portable dependency-free implementation of Minisign signature verification"
  :version "1.0.1"
  :author "Sebastian Melzer <semz@semelz.de>"
  :maintainer "Sebastian Melzer <semz@semelz.de>"
  :licence "MIT"
  :homepage "https://semelz.de/software/minisign-verify.html"
  :depends-on ()
  :components ((:file "minisign-verify")))
