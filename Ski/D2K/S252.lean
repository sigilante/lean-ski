import Ski.D2Base
import Ski.D2K.S251
/-! Generated.  S-law of D: chunks 2016..2023 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2016 : slawChunk 2016 = true := by decide +kernel
theorem slawChunk_2017 : slawChunk 2017 = true := by decide +kernel
theorem slawChunk_2018 : slawChunk 2018 = true := by decide +kernel
theorem slawChunk_2019 : slawChunk 2019 = true := by decide +kernel
theorem slawChunk_2020 : slawChunk 2020 = true := by decide +kernel
theorem slawChunk_2021 : slawChunk 2021 = true := by decide +kernel
theorem slawChunk_2022 : slawChunk 2022 = true := by decide +kernel
theorem slawChunk_2023 : slawChunk 2023 = true := by decide +kernel
theorem slawC_252 (k : Nat) (h1 : 2016 ≤ k) (h2 : k < 2024) : slawChunk k = true := by
  if e2016 : k = 2016 then subst e2016; exact slawChunk_2016 else
  if e2017 : k = 2017 then subst e2017; exact slawChunk_2017 else
  if e2018 : k = 2018 then subst e2018; exact slawChunk_2018 else
  if e2019 : k = 2019 then subst e2019; exact slawChunk_2019 else
  if e2020 : k = 2020 then subst e2020; exact slawChunk_2020 else
  if e2021 : k = 2021 then subst e2021; exact slawChunk_2021 else
  if e2022 : k = 2022 then subst e2022; exact slawChunk_2022 else
  if e2023 : k = 2023 then subst e2023; exact slawChunk_2023 else
  omega
end D2
