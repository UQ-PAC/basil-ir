

theory "Export"

imports 
  Main 
  Test

begin

export_code evalbool in Scala module_name "Test" file_prefix "test/test"

end