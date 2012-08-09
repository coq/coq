#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/callback.h>
#include <caml/fail.h>

#include <gtk/gtk.h>
#include <lablgtk2/wrappers.h>
#include <lablgtk2/ml_glib.h>
#include <lablgtk2/ml_gobject.h>
#include <gtkmacintegration/gtkosxapplication.h>

GtkOSXApplication *theApp;
value open_file_fun, forbid_quit_fun, themenubar, pref_item, about_item;

static void osx_accel_map_foreach_lcb(gpointer data,const gchar *accel_path,
				      guint accel_key, GdkModifierType accel_mods,
				      gboolean changed) {
  if (accel_mods & GDK_CONTROL_MASK) {
    accel_mods |= GDK_META_MASK;
    accel_mods &= (accel_mods & GDK_MOD1_MASK) ? ~GDK_MOD1_MASK : ~GDK_CONTROL_MASK;
    if (!gtk_accel_map_change_entry(accel_path,accel_key,accel_mods,FALSE)) {
      g_print("could not change accelerator %s\n",accel_path);
    }
  }
  if (accel_mods & GDK_MOD1_MASK) {
    accel_mods &= ~ GDK_MOD1_MASK;
    accel_mods |= GDK_CONTROL_MASK;
    if (!gtk_accel_map_change_entry(accel_path,accel_key,accel_mods,FALSE)) {
      g_print("could not change accelerator %s\n",accel_path);
    }
  }
}

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

CAMLprim value caml_gtk_mac_ready(value menubar, value prefs, value about)
{
  GtkOSXApplicationMenuGroup * pref_grp, * about_grp;
  CAMLparam3(menubar,prefs,about);
  themenubar = menubar;
  pref_item = prefs;
  about_item = about;
  caml_register_generational_global_root(&themenubar);
  caml_register_generational_global_root(&pref_item);
  caml_register_generational_global_root(&about_item);
  /*  gtk_accel_map_foreach(NULL, osx_accel_map_foreach_lcb);*/
  gtk_osxapplication_set_menu_bar(theApp,check_cast(GTK_MENU_SHELL,themenubar));
  gtk_osxapplication_insert_app_menu_item(theApp,check_cast(GTK_WIDGET,about_item),1);
  gtk_osxapplication_insert_app_menu_item(theApp,gtk_separator_menu_item_new(),2);
  gtk_osxapplication_insert_app_menu_item(theApp,check_cast(GTK_WIDGET,pref_item),3);
  gtk_osxapplication_insert_app_menu_item(theApp,gtk_separator_menu_item_new(),4);
  gtk_osxapplication_ready(theApp);
  CAMLreturn(Val_unit);
}
