import SatinStress.U1.Certificate.G.Reps
import SatinStress.U1.Certificate.G.TU
import SatinStress.U1.Certificate.G.TL
import SatinStress.U1.Certificate.G.WU
import SatinStress.U1.Certificate.G.WL
import SatinStress.U1.Certificate.G.VU
import SatinStress.U1.Certificate.G.VL
import SatinStress.U1.Certificate.G.DoubleU
import SatinStress.U1.Certificate.G.DoubleL
import SatinStress.U1.Certificate.G.DU
import SatinStress.U1.Certificate.G.DL
import SatinStress.U1.Certificate.G.TraceU
import SatinStress.U1.Certificate.G.TraceL
import SatinStress.U1.Certificate.F.Reps
import SatinStress.U1.Certificate.F.TU
import SatinStress.U1.Certificate.F.TL
import SatinStress.U1.Certificate.F.WU
import SatinStress.U1.Certificate.F.WL
import SatinStress.U1.Certificate.F.VU
import SatinStress.U1.Certificate.F.VL
import SatinStress.U1.Certificate.F.DoubleU
import SatinStress.U1.Certificate.F.DoubleL
import SatinStress.U1.Certificate.F.DU
import SatinStress.U1.Certificate.F.DL
import SatinStress.U1.Certificate.F.TraceU
import SatinStress.U1.Certificate.F.TraceL
import SatinStress.U1.Certificate.X.Reps
import SatinStress.U1.Certificate.X.TU
import SatinStress.U1.Certificate.X.TL
import SatinStress.U1.Certificate.X.WU
import SatinStress.U1.Certificate.X.WL
import SatinStress.U1.Certificate.X.VU
import SatinStress.U1.Certificate.X.VL
import SatinStress.U1.Certificate.X.DoubleU
import SatinStress.U1.Certificate.X.DoubleL
import SatinStress.U1.Certificate.X.DU
import SatinStress.U1.Certificate.X.DL
import SatinStress.U1.Certificate.X.TraceU
import SatinStress.U1.Certificate.X.TraceL
import SatinStress.U1.Sequence

-- The arithmetic pieces put together on the same Class labels and momentum.
namespace SatinStress.U1.Certificate
open Raw (PivotList pick hull)
open Derivative Sequence Class
variable (K : Type*) [Field K] [Algebra K ℂ] [CharZero K]
set_option synthInstance.maxSize 2048

namespace G
theorem tables : Sequence.Tables K ge4 ge5 frequency
    colsTPiv colsWPiv colsVPiv colsTracePiv colsDPiv colsDoublePiv where
  matT := by
    rw [Class.bake, issuers_T, mapped_T]
    exact ⟨by decide, by decide, T_upper K, T_lower K⟩
  matW := by
    rw [Class.bake, issuers_W, mapped_W]
    exact ⟨by decide, by decide, W_upper K, W_lower K⟩
  matV := by
    rw [Class.bake, issuers_V, mapped_V]
    exact ⟨by decide, by decide, V_upper K, V_lower K⟩
  tr := by
    simp only [Class.bake, issuers_T, mapped_T]
    change PivotList K colsTrace colsTracePiv
    exact ⟨by decide, by decide, trace_upper K, trace_lower K⟩
  div := by
    simp only [Class.bake, issuers_T, mapped_T]
    change PivotList K colsD colsDPiv
    exact ⟨by decide, by decide, D_upper K, D_lower K⟩
  comparison := by
    simp only [Class.bake, issuers_W, mapped_W, issuers_V, mapped_V]
    change PivotList K colsDouble colsDoublePiv
    exact ⟨by decide, by decide, double_upper K, double_lower K⟩
  landV := by
    simp only [Class.bake, issuers_T, mapped_T, issuers_V, mapped_V]
    change hull K colsGrad = _
    rw [Raw.pivot_suffices K (grad_upper K),pick_grad,pick_V]; rfl
  landW := by
    simp only [Class.bake, issuers_T, mapped_T, issuers_W, mapped_W]
    change hull K colsLands = _
    rw [Raw.pivot_suffices K (lands_upper K),pick_lands,pick_W]; rfl
end G

namespace F
theorem tables : Sequence.Tables K ph4 ph5 frequency
    colsTPiv colsWPiv colsVPiv colsTracePiv colsDPiv colsDoublePiv where
  matT := by
    rw [Class.bake, issuers_T, mapped_T]
    exact ⟨by decide, by decide, T_upper K, T_lower K⟩
  matW := by
    rw [Class.bake, issuers_W, mapped_W]
    exact ⟨by decide, by decide, W_upper K, W_lower K⟩
  matV := by
    rw [Class.bake, issuers_V, mapped_V]
    exact ⟨by decide, by decide, V_upper K, V_lower K⟩
  tr := by
    simp only [Class.bake, issuers_T, mapped_T]
    change PivotList K colsTrace colsTracePiv
    exact ⟨by decide, by decide, trace_upper K, trace_lower K⟩
  div := by
    simp only [Class.bake, issuers_T, mapped_T]
    change PivotList K colsD colsDPiv
    exact ⟨by decide, by decide, D_upper K, D_lower K⟩
  comparison := by
    simp only [Class.bake, issuers_W, mapped_W, issuers_V, mapped_V]
    change PivotList K colsDouble colsDoublePiv
    exact ⟨by decide, by decide, double_upper K, double_lower K⟩
  landV := by
    simp only [Class.bake, issuers_T, mapped_T, issuers_V, mapped_V]
    change hull K colsGrad = _
    rw [Raw.pivot_suffices K (grad_upper K),pick_grad,pick_V]; rfl
  landW := by
    simp only [Class.bake, issuers_T, mapped_T, issuers_W, mapped_W]
    change hull K colsLands = _
    rw [Raw.pivot_suffices K (lands_upper K),pick_lands,pick_W]; rfl
end F

namespace X
omit [CharZero K] in
theorem tables : Sequence.Tables K mixed4 mixed frequency
    colsTPiv colsWPiv colsVPiv colsTracePiv colsDPiv colsDoublePiv where
  matT := by
    rw [Class.bake, issuers_T, mapped_T]
    exact ⟨by decide, by decide, T_upper K, T_lower K⟩
  matW := by
    rw [Class.bake, issuers_W, mapped_W]
    exact ⟨by decide, by decide, W_upper K, W_lower K⟩
  matV := by
    rw [Class.bake, issuers_V, mapped_V]
    exact ⟨by decide, by decide, V_upper K, V_lower K⟩
  tr := by
    simp only [Class.bake, issuers_T, mapped_T]
    change PivotList K colsTrace colsTracePiv
    exact ⟨by decide, by decide, trace_upper K, trace_lower K⟩
  div := by
    simp only [Class.bake, issuers_T, mapped_T]
    change PivotList K colsD colsDPiv
    exact ⟨by decide, by decide, D_upper K, D_lower K⟩
  comparison := by
    simp only [Class.bake, issuers_W, mapped_W, issuers_V, mapped_V]
    change PivotList K colsDouble colsDoublePiv
    exact ⟨by decide, by decide, double_upper K, double_lower K⟩
  landV := by
    simp only [Class.bake, issuers_T, mapped_T, issuers_V, mapped_V]
    change hull K colsGrad = _
    rw [Raw.pivot_suffices K (grad_upper K),pick_grad,pick_V]; rfl
  landW := by
    simp only [Class.bake, issuers_T, mapped_T, issuers_W, mapped_W]
    change hull K colsLands = _
    rw [Raw.pivot_suffices K (lands_upper K),pick_lands,pick_W]; rfl
end X
end SatinStress.U1.Certificate
