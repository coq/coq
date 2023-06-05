  $ coqdep -Q ./theory1 theory1 -Q ./theory2 theory2 theory1/file1.v
  theory1/file1.vo theory1/file1.glob theory1/file1.v.beautified theory1/file1.required_vo: theory1/file1.v ./theory1/dir/file2.vo ./theory2/file3.vo
  theory1/file1.vio: theory1/file1.v ./theory1/dir/file2.vio ./theory2/file3.vio
  $ coqdep -Q ./theory1 theory1 -Q ./theory2 theory2 theory1/dir/file2.v
  theory1/dir/file2.vo theory1/dir/file2.glob theory1/dir/file2.v.beautified theory1/dir/file2.required_vo: theory1/dir/file2.v ./theory2/file3.vo
  theory1/dir/file2.vio: theory1/dir/file2.v ./theory2/file3.vio
  $ coqdep -Q ./theory1 theory1 -Q ./theory2 theory2 theory2/file3.v
  theory2/file3.vo theory2/file3.glob theory2/file3.v.beautified theory2/file3.required_vo: theory2/file3.v 
  theory2/file3.vio: theory2/file3.v 
