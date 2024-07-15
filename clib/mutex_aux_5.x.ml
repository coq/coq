let with_lock m ~scope = Mutex.protect m scope
