(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type color = GDraw.color

type model_event = [ `INSERT | `REMOVE | `SET of int * color ]

class type segment_signals =
object
  inherit GObj.misc_signals
  inherit GUtil.add_ml_signals
  method clicked : callback:(int -> unit) -> GtkSignal.id
end

class type model =
object
  method changed : callback:(model_event -> unit) -> unit
  method length : int
  method fold : 'a. ('a -> color -> 'a) -> 'a -> 'a
end

class segment : unit ->
  object
    inherit GObj.widget
    val obj : Gtk.widget Gtk.obj
    method set_model : model -> unit
    method connect : segment_signals
    method default_color : color
    method set_default_color : color -> unit
  end
