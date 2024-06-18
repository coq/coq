let declare_definition ~poly name sigma body =
  let cinfo = Declare.CInfo.make ~name ~typ:None ~opaque:(Some false) () in
  let info = Declare.Info.make ~poly () in
  Declare.declare_definition ~info ~cinfo ~body sigma
