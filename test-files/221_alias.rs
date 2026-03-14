trait MyTrait<'a> {
    type Assoc<'b> where 'a: 'b;
    
    fn get_assoc<'slf, 'b>(&'slf mut self) -> Self::Assoc<'b> {
      todo!()
    }
}