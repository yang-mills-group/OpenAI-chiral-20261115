import YM.SU5.FiniteGaugeData.Tower.Pool
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
/-!
# Entire resolution Hilbert can see real time -- no arbitrary continuity
projection at zero

First show that every admitted marked vector at any fixed level is already
at *strictly positive time* on this same hierarchy. Issue a strict extra
margin of at least 1 per lift on one step (accumulates, even for stencils
of large extent into the infinite-volume limit; all Fock costs fixed).
Thus can represent every actor in range of a strictly positive-time transfer.
Apply standard contraction/symmetry Euclidean energy argument through this
fact (see TimeKeeper). No analogous assertion here for would-be arbitrarily
high resolution distribution-valued fields, or analytic continuation and
boosts. Grade prices for other claims still to come.
-/
open scoped InnerProductSpace
open Fock Heat
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}(Q:Resolution (E:=E) Y H D)
variable (j:Axis)(z:ℤ)(strict:Bool)
local notation "m" x:max=> meshface (Λ:=Λ) z x
variable (C:Arena Y H Q j z strict)
local notation "T" s:max=> Tower.Field Y H s j z strict
local notation "κ" s:max=>actor Y H s Q j z strict C
local notation "A"=> Ark.Ht Y H Q j z strict C

local notation "P"=> (tent Y H)
local notation "L"=> Λ.R.L.val
local notation "W"=> reserve Λ l
local notation "ρ"=> L*gross (aliasLaw Λ) (distanceLaw l) Λ.R.J
local notation "R"=> wingspan Λ l
lemma width_margin(Λ':Preparation)(l':ℕ): let v₀:=Λ'.R.L.val; let f₀:=reserve Λ' l'; let h₀:=v₀*gross (aliasLaw Λ') (distanceLaw l') Λ'.R.J
 f₀+1+h₀ ≤ v₀*f₀ := by
 intro Lx Wp rp
 have ht:=Λ'.R.coarse
 let q:=aliasLaw Λ'; let d:= distanceLaw l'; let J:= Λ'.R.J
 change 3≤Lx at ht
 change Wp+1+Lx * (beforePad q+d+10*(J+3))≤Lx*Wp
 unfold beforePad
 change _≤ _ -- reserve expand
 have hp:Wp=16*(100*Lx*(1+q)+d+J+10)+1:=by unfold Wp Journey.reserve r₃ r₁; dsimp only [Lx,d,J,q]; ring
 rw [hp]
 have hf: 3*Lx*(1+q) ≤ Lx*Lx*(1+q):=by gcongr
 have hg: 3*(J+d) ≤ Lx*(J+d):=by gcongr
 -- J term need tighter separate
 have hj:3*J ≤ Lx*J:=by gcongr
 have hd:3*d ≤ Lx*d:=by gcongr
 nlinarith
lemma strict_one{n:ℕ}{c:ℤ}{S:Finset Cover} (h:region j c ((P).ℓ+n) S):region j (L*c) ((P).ℓ+n+1) (R S):=by
 have hu:=width_margin Λ l; dsimp only at hu; change W+1+ρ ≤ L*W at hu; have p:(P).ℓ=W:=rfl
 intro x t; obtain ⟨i,v,g⟩:=mem_biUnion.mp t; obtain ⟨i,u,rfl⟩:=mem_image.mp v; obtain ⟨bV,v,rfl⟩:=mem_image.mp g
 specialize h i u; rw [Pi.add_apply,Pi.smul_apply,nsmul_eq_mul]; have hb:= (Lattice.box_test.mp v).1 j
 let L':ℤ:=L; let k:ℤ:= W; let n':ℤ:= n
 have hL:1 ≤ L':=by unfold L'; exact_mod_cast Λ.R.L.property
 have hK: (c+(k+n')) *L'≤ i j*L':= mul_le_mul_of_nonneg_right (by unfold k n'; push_cast at h; exact h) (by linarith)
 have hρ: k+1+(ρ:ℕ) ≤ L'*k:=by unfold L' k; exact_mod_cast hu
 have ht:L' * n' ≥ n' := le_mul_of_one_le_left (by unfold n'; positivity) hL
 change L'*c+((W+n+1:ℕ):ℤ) ≤ bV j+L'*i j
 rw [Nat.cast_add,Nat.cast_add,Nat.cast_one]; change -((ρ:ℕ):ℤ) ≤ bV j at hb; unfold k n' at *; nlinarith
include Q
lemma increase(S:Finset Cover)(h:region j (meshface (Λ:=Λ) z s) (P).ℓ S)(r:ℕ):region j (m (s+r)) ((P).ℓ+r) (volumeAround Λ l r S):=by
 induction r with
 | zero=> simpa [volumeAround] using h
 | succ a ih=>
    rw [volumeAround]; have ht:=strict_one Y H j ih; rw [←Nat.add_assoc,←Nat.add_assoc _ a, show (m (s+a+1))=L*(m (s+a)) from ?_]; swap; · unfold meshface; rw [pow_succ']; ring
    exact ht

-- admits signed-matter negative travel when plenty of slack (double step
-- rather than single for unconditional positivity in applying ripple).
lemma predecessor (x:T s): ∃ (q:ℕ)(y:T (s+q)), tick Y H (s+q) j z strict 2 y = Raise Y H Q j z strict s (s+q) (by omega) x:=by
 obtain ⟨v₀,Hw⟩:= (purpose_ok ..).mp x.property
 obtain ⟨X,t,v⟩:= (v₀:∃ S:Finset Cover,InTest (tent Y H) true _ false (x.val)∧ region j (m s) (P).ℓ S)
 let q:= 16*Λ.block.val
 let V:=volumeAround Λ l q X; let Z:=stream Y H D s q x.val
 let F:=Raise Y H Q j z strict s (s+q) (by omega) x
 have ht: F.val=Z:=by change stream Y H D s (s+q-s) _= _; rw [show s+q-s=q by omega]
 have hZ:InTest (tent Y H) true V false F.val:=ht.symm ▸ (proceeds Y H Q s q t).1
 have hv0:region j (m (s+q)) ((P).ℓ+q) V:=increase Y H s Q j z X v q
 let k:ℤ:=gaugeShift Λ.block 2
 let F₀:= chime (tent Y H) j (-k) F.val
 have hf:=((purpose_ok ..).mp F.property).2
 have he:region j (m (s+q)) (P).ℓ (address j (-k) V):=by
    intro i t; obtain ⟨i,v,rfl⟩:= mem_image.mp t; specialize hv0 i v; simp; unfold q at hv0 ⊢; unfold k gaugeShift; omega
 let t0:(T (s+q)):=⟨F₀,(purpose_ok ..).mpr ⟨(show _ from ⟨_,flow_port (tent Y H) j (-k) hZ,he⟩),fun a=>chime_cov _ _ _ hZ (hf a)⟩⟩  -- notation T clash
 refine ⟨q,t0,Subtype.ext ?_⟩; change chime _ j k F₀= _; unfold F₀; rw [Tower.bumps (tent Y H) j k (-k) hZ,add_neg_cancel,wake _ j hZ]

include V C
lemma nowPositive (x:T s):∃ (r:ℕ)(y:T r), (κ s) x=ripple Y H V r Q j z strict C 2 ((κ r) y):=by
 obtain ⟨r,y,h⟩:=predecessor Y H s Q j z strict x
 exact ⟨s+r,y,by rw [limited_time Y H V (s+r) Q j z strict C 2 le_rfl y,amount_reset,h,join_actor Y H V]⟩
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.nowPositive
