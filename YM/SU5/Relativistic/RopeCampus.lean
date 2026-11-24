import YM.SU5.Relativistic.RopeLimits
set_option autoImplicit false
set_option synthInstance.maxSize 25000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
namespace FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat PhaseChoice SlabMark Vacancy Tapestry Tapestry.Altitude Tapestry.Exhibition Tower.Selected
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H a b I E)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{i k:ℕ→ℕ}(Q:Coherent Y H (i:=a) (k:=b) (E:=E) D i k)
variable (u:ℕ→ℕ)(T:ℕ→ Bool→Family (tent Y H)→Family (tent Y H))(t:GradesAll (i:=a) (a:=i) (k:=b) (b:=k) Y H u T)
local notation "W"=> wingspan Λ l


variable (s n:ℕ)(X:ℕ→ Finset Cover)
local notation "A" r:max=> a (i (u r))
local notation "B" r:max=> b (k (u r))
namespace Lariat

local notation "τ"=>s+n
local notation "E₀" f:max=> rideL Y H T s f
local notation "U" m:max f:max=> priceAt Y H s (A m) (B m) f

-- finite compression to selected in Boundary. For now exact unselected in fixed one series, uniform price. x/y based on Cover test literal values uniform Costs-even. Odd gives automatic limiting zero. E already specified at even. For E' use same.
def discount {K':Calibration} (E:ℕ→Family K'→ℂ) (v:Bool)(s:ℕ)(f:Family K'):ℂ:= if v=true then 0 else E s f
include V Q t
lemma admits_all (C':ℝ)(p:0<C') (δ:ℝ) (m':0<δ): ∀ᶠ r:ℕ in atTop,∀ f:Lariat (tent Y H) n,Costs X f → priced (fun _=> C') f →
    ‖sharp Y H (s+n) (a (i (u r))) (b (k (u r))) (priceAt Y H s (a (i (u r))) (b (k (u r))) f)-discount E (hue f) (s+n) (rideL Y H T s f)‖ ≤ δ:=by
 obtain ⟨c,v,h⟩:=cashLine Y H V Q u T t s n X C' p
 let A₀:= runningBox Λ l X n
 obtain ⟨e,w,hp⟩:= Q.implements τ A₀
 have he:= t.thins.tendsto_atTop
 have H' := V.pick.grow_k.tendsto_atTop.comp (Q.growsB.tendsto_atTop.comp he)
 let L:=toll Y H τ A₀; have hw:0 ≤ L:=(toll_pays ..).1; let d:= δ/2/c; let z:=δ/2/(1+L)
 have hD: 0<d:=by unfold d; positivity; -- tactic
 have hZ:0<z:=by unfold z; positivity
 filter_upwards [he.eventually (Q.finance τ), h z hZ,he.eventually (hp _ hD),H'.eventually (odd_bill Y τ d hD)] with r i' Kx h u0 f tA f'
 let q:= E₀ f; let g:= U r f
 obtain ⟨hh,v',y⟩:= Kx _ tA f'
 have e: f.box Λ l=A₀:= hires _ _ tA
 have hx: InTest K true A₀ (hue f) g:= e ▸ groundPrice Y H s _ _ _
 have hz: InTest K true A₀ (hue f) q:= e ▸ aboard Y H u T t s f -- u shadows
 cases t': hue f
 · simp only [t'] at hx hz; rw [discount,if_neg (by decide)]; have hOp := h _ hx c v'; apply le_trans (norm_sub_le_norm_sub_add_norm_sub _ (E τ g) _); have hP: ‖E τ g-E τ q‖≤L*z:=by rw [← E_sub Y H V τ (aux_test hx) (aux_test hz)]; exact E_bound Y H V τ A₀ (inLess hx hz) y
   refine (add_le_add hOp.2.2.2.2.1 hP).trans ?_
   have Hh:z*(1+L)=δ/2:= div_mul_cancel₀ _ (by linarith); rw [show d*c=δ/2 from div_mul_cancel₀ _ v.ne']; nlinarith
 rw [discount,if_pos rfl,sub_zero]
 rw [t'] at hx
 have vv(S:Finset Cover) {b c:Side}(t:b=c)(V:Mark b)(x:ℝ)(p:∀ u, ‖V u‖≤x):∀ u,‖ship t V u‖≤x:=by subst c; exact p
 have hk:= u0 _ i' _ (distribute Y H τ (A r) g) (parked Y H τ _ _ hx) c (vv A₀ (terrain Y H ..) _ c (v' _)); exact hk.trans ((div_mul_cancel₀ _ v.ne').le.trans (by linarith only [m']))

end Lariat
end FermionSlab
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
