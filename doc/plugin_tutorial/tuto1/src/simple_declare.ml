let declare_definition ~poly name sigma body =
  let cinfo = Declare.CInfo.make ~name ~typ:None () in
  let info = Declare.Info.make ~poly () in
  Declare.declare_definition ~info ~cinfo ~opaque:false ~body sigma
