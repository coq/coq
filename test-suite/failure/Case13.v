Type [x:nat]<nat> Cases x  of 
                  ((S x) as b) => <nat>Cases x  of
                                        x => (S b x)
                                   end
                          end.
