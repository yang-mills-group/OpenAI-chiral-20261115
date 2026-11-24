import YM.SU5.Relativistic.Unbone
import YM.SU5.Relativistic.Fusing
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat PhaseChoice SlabMark Vacancy Tapestry Tapestry.Altitude Tapestry.Exhibition Tower.Selected
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{L:Rack Λ l}{B:Clay Λ l}
    (D : Exhibition Y H a b I E L B)
local notation "V"=>D.univ_
variable (G:SatinVerification.GroundExtension (i:=a) (k:=b) (E:=E) Y H)
variable (u:ℕ→ℕ) {T:ℕ→Bool→Family (tent Y H)→Family (tent Y H)}(t:GradesAll (i:=a) (a:=G.rows) (k:=b) (b:=G.columns) Y H u T)
variable (d j:Axis) (c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)
variable (x:displayAlgebra Y H D.univ_ G.history G.clipped d false (c d)→⋆ₐ[ℂ] ℂ)
local notation "χ" i:max=> displacement Y H D.univ_ G.history G.clipped d false (c d) x i (c i)
local notation "ψ"=>evaluate Y H D.univ_ G d c (SameCharacter.resident Y H D.univ_ G d false (c d) x)
local notation "D₀"=> Dome (tent Y H)
local notation "Ξ"=> Cloud (Dome (tent Y H))
local notation "φ" n:max => response Y H V n G.history G.clipped j false (c j) (χ j)
local notation "P" s:max F:max=>stream Y H (fun s=>T s true) s F
local notation "Q"=> G.history
variable (s:ℕ)
local notation "α" => walkV Y H j
local notation "F₀"=> Cabin (tent Y H) j
local notation "κ" u:max=>mirror K j u
local notation "Λ₀"=> Λ.R.L.val
local notation "B₁" s:max=> creed Y H D G d j c x s

open HostLegal MeshClock
local notation "R₁"=> timeMesh Λ
local notation "U"=>flier Y H D G u t d j c x
local notation "W₀" s:max=> Tower.Field Y H s j 0 false
local notation "Ωe"=> doorstep Y H V Q G.clipped j false (c j) (χ j)
local notation "Φ" s:max=> arriving Y H V s Q G.clipped j false (c j) (χ j)
local notation "Υ" s:max=> (U).entry s
local notation "E₁"=> indoor Y H V Q G.clipped j false (c j) (χ j)
local notation "E₂"=> (U).booth
local notation "Δ₀"=> relocate (tent Y H)
local notation "B₀"=> ruler Λ.block
open Germ CF.Pannier.Chancel.ScreeV
lemma flog (Z:Calibration)(A:Finset Cover)(p:A.Nonempty)(k:Axis)(i:ℤ): (plow Z k i A).Nonempty:= (_root_.Finset.image_nonempty.mpr p) -- plow maybe not image
lemma rag (A:Finset Cover)(p:A.Nonempty)(k:Axis): (reflectedBox k 0 A).Nonempty:= Finset.image_nonempty.mpr p
variable (Z:Calibration)(k c':Axis)(p:k≠ c'){r:ℕ}{z:ℤ}{S T':Finset Cover}
lemma walksJ (n:ℤ)(h:Till Z r k z S T') : Till Z r k (z+n) (plow Z k n S) (plow Z k n T'):=by
 constructor
 · intro i a; obtain ⟨x,v,w⟩:=plow_stays Z k n S a
   rw [w,moves,if_pos rfl,mul_add]; have ht:=h.stay x v; linarith
 intro i a; obtain ⟨x,v,w⟩:=plow_stays Z k n T' a; rw [w,moves,if_pos rfl,mul_add]; have ht:=h.start x v; linarith
lemma turnedJ (h:Till Z r k z S T'): Till Z r k (-z) (reflectedBox k 0 T') (reflectedBox k 0 S):=by
 constructor
 · intro i w; obtain ⟨x,v,rfl⟩:=mem_image.mp w; rw [fling_move,if_pos rfl,mul_neg]; have h:=h.start x v; omega
 intro i w; obtain ⟨x,v,rfl⟩:=mem_image.mp w; rw [fling_move,if_pos rfl,mul_neg]; have h:=h.stay x v; omega
local notation "L"=> ℕ ×ℕ
local notation "μ" S:max=> reflectedBox k 0 S
local notation "γ" m:max S:max=> plow Z k ((m).1:ℤ) (plow Z c' ((m).2:ℤ) S)
include p
lemma hallway (m:L) (A:Finset Cover){x:Cover}(v:x∈γ m A):∃ y∈A,x k=y k+ ruler Z.B*m.1 ∧ x c'=y c'+ruler Z.B*m.2:=by
 obtain ⟨x',b,h⟩:=plow_stays Z k _ _ v; obtain ⟨y,a,g⟩:= plow_stays Z c' _ _ b; exact ⟨y,a,by rw [h,moves,g,moves,if_pos rfl,if_neg p],by rw [h,moves,g,if_neg p.symm,moves,if_pos rfl]⟩
lemma ticketTill (j':Axis)(h:j'=k∨j'=c') (S T':Finset Cover)(r:ℕ): ∀ᶠ m:L in atTop, ∃z:ℤ, Till Z r j' z (μ S) (γ m T'):=by
 let W:=μ S
 obtain ⟨a,b⟩:= Tower.sizes W; obtain ⟨s,t⟩:= b j'; obtain ⟨d,p'⟩:= Tower.sizes T'; obtain ⟨s',v⟩:=p' j'
 let u:= s+a; have hW(y:Cover)(p:y∈ W): y j'≤ u:= (t y p).2
 let n:=u+zig Z r-(s':ℤ)+d; let l:=n.toNat
 filter_upwards [eventually_ge_atTop ((l,l):ℕ×ℕ)] with m hL
 refine zig_here W (γ m T') r j' u hW (fun y z=>?_)
 obtain ⟨x',xV,x₀,x₁⟩:= hallway Z k c' p m T' z
 have hx:= ruler_gene Z.B; have hp : n ≤ (l:ℤ):= Int.self_le_toNat _
 rcases h with rfl|rfl
 · rw [x₀]; have he: l≤ m.1:=hL.1; have hL0:s' ≤ x' j':=(v x' xV).1; have hd:(m.1:ℤ)≤ ruler Z.B*m.1:= le_mul_of_one_le_left (by positivity) hx; unfold n at hp; omega
 rw [x₁]; have he: l≤ m.2:=hL.2; have hL0:s'≤ x' j':=(v x' xV).1; have hd:(m.2:ℤ)≤ruler Z.B*m.2:= le_mul_of_one_le_left (by positivity) hx; unfold n at hp; omega
-- l≤ m token issue
omit p
variable {Z} (a₀ b':Electrum (tent Y H))
noncomputable def wrapped : Electrum (tent Y H):= ⟨μ a₀.S,mirror K k 0 a₀.f,a₀.gear,axial K k 0 a₀.paid,rag _ a₀.gr k⟩
noncomputable def decant (m:ℕ×ℕ): Electrum (tent Y H):= ⟨plow K k m.1 (plow K c' m.2 a₀.S), Δ₀ k m.1 (Δ₀ c' m.2 a₀.f),a₀.gear,froll k (froll c' a₀.paid _) _,flog K _ (flog K _ a₀.gr _ _) _ _⟩
local notation "V'" a:max=> wrapped Y H k a
local notation "D'" m:max a:max=> decant Y H k c' a m
variable (θ:0<r)
include p θ
lemma morning_left (u:Till K r k z a₀.S b'.S): ∀ᶠ m:L in atTop, CircleH Y H k s (V' a₀) (D' m a₀) (V' b') (D' m b') ∧ CircleH Y H k s (V' b') (D' m b') (V' a₀) (D' m a₀):=by
 filter_upwards [ticketTill (tent Y H) k c' p k (Or.inl rfl) a₀.S a₀.S r] with m ⟨z,g⟩
 have hx:= walksJ K k (m.1:ℤ) (walksGap k c' (Ne.symm p) K (m.2:ℤ) u); have h:=turnedJ K k u
 refine ⟨⟨V' b',V' a₀,D' m a₀,D' m b',?_,slotTill Y H k s h θ,slotTill Y H k s g θ,slotTill Y H k s hx θ⟩,⟨V' b',V' a₀,D' m a₀,D' m b',?_,slotTill Y H k s h θ,slotTill Y H k s g θ,slotTill Y H k s hx θ⟩⟩
 · exact permBolt _ _ _ _
 exact permBolt' _ _ _ _
where 
  permBolt (a b c d:Electrum K): List.Perm [a, b, c, d] [c, a, b, d] := by
    let f:Fin 4→Electrum K := ![a,b,c,d]; have ht:List.Perm ([0, 1, 2, 3]:List (Fin 4)) [2, 0, 1, 3]:=by decide
    simpa [f] using ht.map f
  permBolt' (a b c d:Electrum K): List.Perm [c, d, a, b] [c, a, b, d] := by
    let f:Fin 4→Electrum K := ![a,b,c,d]; have ht:List.Perm ([2, 3, 0, 1]:List (Fin 4)) [2, 0, 1, 3]:=by decide
    simpa [f] using ht.map f
lemma evening_left (u:Till K r c' z a₀.S b'.S): ∀ᶠ m:L in atTop, CircleH Y H c' s (V' a₀) (D' m a₀) (V' b') (D' m b') ∧ CircleH Y H c' s (V' b') (D' m b') (V' a₀) (D' m a₀):=by
 filter_upwards [ticketTill K k c' p c' (Or.inr rfl) b'.S a₀.S r] with m ⟨z,g⟩
 have hx:= walksGap c' k p K (m.1:ℤ) (walksJ K c' (m.2:ℤ) u); have h:=turnedGap c' k p K (0:ℤ) u
 refine ⟨⟨V' a₀,V' b',D' m a₀,D' m b',?_,slotTill Y H c' s h θ,slotTill Y H c' s g θ,slotTill Y H c' s hx θ⟩,⟨V' a₀,V' b',D' m a₀,D' m b',?_,slotTill Y H c' s h θ,slotTill Y H c' s g θ,slotTill Y H c' s hx θ⟩⟩
 · exact permBolt _ _ _ _
 exact permBolt' _ _ _ _
where 
  permBolt (a b c d:Electrum K): List.Perm [a, b, c, d] [a, c, b, d] := by
    let f:Fin 4→Electrum K := ![a,b,c,d]; have ht:List.Perm ([0, 1, 2, 3]:List (Fin 4)) [0, 2, 1, 3]:=by decide
    simpa [f] using ht.map f
  permBolt' (a b c d:Electrum K): List.Perm [c, d, a, b] [a, c, b, d] := by
    let f:Fin 4→Electrum K := ![a,b,c,d]; have ht:List.Perm ([2, 3, 0, 1]:List (Fin 4)) [0, 2, 1, 3]:=by decide
    simpa [f] using ht.map f
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.morning_left
