import YM.SU5.Relativistic.CorridorRaw
/-!
# Geometry registration of local physical polynomials.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5500
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Set Filter MeasureTheory Metric
open Lattice Wilson RG SU Lat Mir RP Reflect Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Py Py.Rate LocalLimit PhaseChoice Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy MeshClock Selected
open Tapestry Tapestry.Altitude Tapestry.Exhibition
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
    {L:Rack Λ l}{B:Clay Λ l}(D : Exhibition Y H a b I E L B)(G:SatinVerification.GroundExtension (i:=a) (k:=b) (E:=E) Y H)
variable (j:Axis) (J: Arena Y H G.history.circuit j 0 false)
local notation "M"=> timeMesh Λ
local notation "N" i:max z:max=> notch M i z
local notation "D₀"=> Dome (tent Y H)
local notation "Τ"=> Cloud (Dome (tent Y H))
local notation "P₀" n:max=> vistaFinish Y H n D
local notation "d★" => vistaDressing Y H D
local notation "B₀" => driveAlgebra Y H D.univ_ G.history G.clipped j false J
local notation "Rg" t:max => Docked Y H D.univ_ t G.history G.clipped j J

local notation "ρ"=> D.univ_
local notation "reach" n:max f:max => reachMark (tent Y H) ((P₀ n) f)
section billing
variable (d:Axis)(c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)(χ : displayAlgebra Y H D.univ_ G.history G.clipped d false (c d) →⋆ₐ[ℂ] ℂ)
local notation "χ̂" j:max=> displacement Y H D.univ_ G.history G.clipped d false (c d) χ j (c j)
local notation "Χ"=> SameCharacter.resident Y H D.univ_ G d false (c d) χ
local notation "Ψ"=> onDrawing Y H D.univ_ G D d c Χ
local notation "Θ"=> procession Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "Ρ"=>indoor Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "V"=>fort Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "p★"=>saunters Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "ω"=> vocation Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "Ω"=> doorstep Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "A"=>ride Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "Ξ"=> peninsula Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "E□"=> encase Y H D.univ_ G.history G.clipped j (c j) (χ̂ j)
local notation "P□"=> mainsea Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "e□"=> follows_road Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "B□"=> docket Y H D G j (c j)
local notation "Φ"=> driveAlgebra Y H D.univ_ G.history G.clipped j false (c j)
local notation "dock" n:max => Docked Y H D.univ_ n G.history G.clipped j (c j)
local notation "Zg" t:max => (Axis→Fin ((timeMesh Λ).L^t))

variable {I':Type*}(f:I'→ Cloud (Dome (tent Y H)))
variable (t:I'→ℕ)(S T:I'→ Slab (timeMesh Λ)) (l':List I')(b₁: Stamp (timeMesh Λ))
local notation "EE" i:max z:max => envelope (P□) (A) (e□) (Θ (B□ (t i) (f i) (S i))) (S i) (T i) z
local notation "Q₀" g:max=> packetEnvelope Y H D G j d c χ f t S T g l' b₁
local notation "ϕ" v:max=> integerRead v
local notation "GΛ"=> Axis → Stamp (timeMesh Λ)
local notation "R★" q:max=> rawRoom Y H D G j d c χ f l' b₁ T t S q
variable (u:I'→Axis→ℝ)
local notation "cm" t:max S:max T:max l:max b:max u:max=> Corridor Y H j f t S T l b u
lemma alongRow {I: Type*}{M':MeshClock.Mesh} (T : I → Slab M') (w: Stamp M') (l:List I) (h:inRow T w l) (i:I)(p:i∈l): w≤ (T i).lower:=by
 induction l generalizing w with
 | nil=>contradiction
 | cons a l ih=>
    rcases List.mem_cons.mp p with u|u
    · rw [u]; exact h.1
    exact (le_trans h.1 (T a).thick.le).trans (ih _ h.2 u)

include G in
lemma fuse_physical {n:ℕ}{U W:Set RSpace}{x y:Tapestry.Altitude.Cloud (Dome (tent Y H))}(p: x∈ poet Y H n U)(z:y∈ poet Y H n W)(g:Disjoint U W): vistaFinish Y H n D (x*y)= vistaFinish Y H n D x * vistaFinish Y H n D y:=by
 apply depart_pair Y H D.univ_ G D (U:=handstamp U) (W:=handstamp W) (a:=Set.Iic n) (b:=Set.Iic n) ?_ ?_ (Disjoint.preimage _ g) <;> rw [inter_self]
 · exact ((well_spec ..).1 p).1
 exact ((well_spec ..).1 z).1
lemma enclosed (n:ℕ)(X:Set RSpace)(h:∀ i∈l', f i∈ poet Y H n X): (l'.map f).prod∈ poet Y H n X:=by
 induction l' with
 | nil=> exact Subalgebra.one_mem _
 | cons i l ih=> exact (poet Y H n X).mul_mem (h i List.mem_cons_self) (ih fun i p=> h i (List.Mem.tail _ p))
lemma zeroLocated (p:cm t S T l' b₁ 0) (i:I')(x:i∈ l'): (f i)∈ poet Y H (t i) {v : RSpace| ((T i).lower:ℝ)<v j∧ v j<((T i).upper:ℝ)}:=by
 obtain ⟨U,k,z,h⟩:= (p.issued i x).regionHere
 apply circum_widens Y H _ Subset.rfl z -- orientation
 intro u hu; refine ⟨(lt_of_lt_of_le ?_ (h hu).1),(lt_of_le_of_lt (h hu).2 ?_)⟩
 · simpa using (p.assured i x).1
 simpa using (p.assured i x).2
include G in
lemma zenith (p:cm t S T l' b₁ 0) (n:ℕ) (g:∀ i∈l', t i ≤ n) :
    vistaFinish Y H n D ((l'.map f).prod)= (l'.map (fun i=> vistaFinish Y H n D (f i))).prod := by
 let X(i:I'):= {v:RSpace| ((T i).lower:ℝ)<v j ∧ v j <((T i).upper:ℝ)}
 induction l' generalizing b₁ with
 | nil=>
    -- uses unit of Vista
    change (P₀ n) 1=1; apply Decking.crown1 -- tune
 | cons i l ih=>
    have hp: cm t S T l ((T i).upper) 0:=⟨p.vault.2,fun j u=> p.issued j (List.Mem.tail _ u), fun j u=> p.assured j (List.Mem.tail _ u)⟩
    have hh(k:I')(u:k∈i::l): f k∈ poet Y H n (X k):= circum_widens Y H Set.Subset.rfl (Set.Iic_subset_Iic.mpr (g k u)) (zeroLocated Y H j f t S T (i::l) b₁ p k u)
    rw [List.map_cons,List.prod_cons, List.map_cons,List.prod_cons, fuse_physical Y H D G (W:={x:RSpace| ((T i).upper:ℝ) ≤ x j}) (hh _ List.mem_cons_self)]
    · rw [ih _ hp _]; exact fun i u=>g i (List.Mem.tail _ u)
    · apply enclosed
      intro k u; apply circum_widens Y H _ Set.Subset.rfl (hh k (List.Mem.tail _ u))
      intro v w
      exact (show ((T i).upper:ℝ)≤ ((T k).lower:ℝ) from alongRow T _ _ hp.vault k u).trans w.1.le
    exact Set.disjoint_left.mpr fun i z h=> not_lt_of_ge h z.2
lemma fitCostZero (p:cm t S T l' b₁ 0): rawRoom Y H D G j d c χ f l' b₁ T t S 0= Ψ ((l'.map f).prod) := by
  have hp : Corridor Y H j f t S T l' b₁ (integerRead (M':=M) (0:I'→Axis→Stamp M)):=p
  have hg : ∀ᶠ n in atTop,∀ i∈l', t i ≤ n:=by simp_rw [←List.mem_toFinset]; exact (eventually_all_finset _).mpr fun i _=> eventually_ge_atTop _
  obtain ⟨n,e,g⟩:= ((hp.buyExact Y H D G j d c χ f t S T l' b₁ 0).and hg).exists
  -- recover all pinhole shift at zero equals product of P0. source short.
  have hh : ((l'.map f).prod)∈ shorter (Dome (tent Y H)) n := listProducts _ _ (fun i v=> Altitude.climbs D₀ (g i v) ( (p.issued i v).shortCut Y H j (t i) (f i) (S i)))
  let z(i:I') : Cover:= fun j : Axis=> tags n ((0:I'→Axis→ Stamp M) i j)
  have hx(i:I'): z i=0:= funext (fun j=> by change tags n (0:Stamp M)=0; exact (notch_zero M n) ▸ tags_lock M n 0)
  have he(i:I'): signOver Y H D n (z i) (f i)= pinhole (Dome (tent Y H)) n (vistaFinish Y H n D (f i)):=by rw [hx]; unfold signOver migrate; rw [world_seed]; rfl
  change Ψ ((l'.map (fun i=>signOver Y H D n (z i) (f i))).prod)=_ at e
  have hz: pinhole (Dome K) n (vistaFinish Y H n D ((l'.map f).prod))=(l'.map (fun i=>signOver Y H D n (z i) (f i))).prod:=by simp_rw [he]; rw [zenith Y H D G j f t S T l' b₁ p n g,map_list_prod,List.map_map]; rfl
  rw [←e,←hz]; exact (plugged ..).trans ((show Ψ (l'.map f|>.prod)= evaluate Y H D.univ_ G d c Χ n ((P₀ n) _).val from drawAt Y H D.univ_ G D d c Χ hh).symm)
where
 listProducts (l:List I')(n:ℕ)(g:∀i∈l,f i∈shorter (Dome (tent Y H)) n) : (l.map f).prod∈shorter (Dome (tent Y H)) n:=by
  induction l with
  | nil=> exact (shorter _ _).one_mem
  | cons i l ih=> exact (shorter _ _).mul_mem (g _ List.mem_cons_self) (ih (fun _ h=> g _ (List.Mem.tail _ h)))
end billing
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.fitCostZero
