import FastHTTP.SSE

namespace FastHTTP.SSE

/-- WHATWG HTML SSE data-field wire form for data containing no line break.
This covers the allocation-saving branch of the actual Event encoder. Optional
id/event/retry fields and multiline normalization have separate runtime tests. -/
theorem single_line_data_wire (data : String)
    (noCR : data.contains '\r' = false) (noLF : data.contains '\n' = false) :
    ({ data } : Event).encode = .ok ("data: " ++ data ++ "\n\n").toUTF8 := by
  simp [Event.encode, noCR, noLF, String.append_assoc]
  rfl

end FastHTTP.SSE
