#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/callback.h>
#include <caml/fail.h>

#include <igemacintegration/gtkosxapplication.h>

GtkOSXApplication *theApp;
value open_file_fun, forbid_quit_fun;

static gboolean deal_with_open(GtkOSXApplication *app, gchar *path, gpointer user_data)
{
  CAMLparam0();
  CAMLlocal2(string_path, res);
  string_path = caml_copy_string(path);
  res = caml_callback_exn(open_file_fun,string_path);
  gboolean truc = !(Is_exception_result(res));
  CAMLreturnT(gboolean, truc);
}

static gboolean deal_with_quit(GtkOSXApplication *app, gpointer user_data)
{
  CAMLparam0();
  CAMLlocal1(res);
  res = caml_callback_exn(forbid_quit_fun,Val_unit);
  gboolean truc = (Bool_val(res))||((Is_exception_result(res)));
  CAMLreturnT(gboolean, truc);
}

CAMLprim value caml_gtk_mac_init(value open_file_the_fun, value forbid_quit_the_fun)
{
  CAMLparam2(open_file_the_fun,forbid_quit_the_fun);
  open_file_fun = open_file_the_fun;
  caml_register_generational_global_root(&open_file_fun);
  forbid_quit_fun = forbid_quit_the_fun;
  caml_register_generational_global_root(&forbid_quit_fun);
  theApp = g_object_new(GTK_TYPE_OSX_APPLICATION, NULL);
  g_signal_connect(theApp, "NSApplicationOpenFile", G_CALLBACK(deal_with_open), NULL);
  g_signal_connect(theApp, "NSApplicationBlockTermination", G_CALLBACK(deal_with_quit), NULL);
  CAMLreturn (Val_unit);
}

CAMLprim value caml_gtk_mac_ready(value unit)
{
  CAMLparam1(unit);
  gtk_osxapplication_ready(theApp);
  CAMLreturn(Val_unit);
}
