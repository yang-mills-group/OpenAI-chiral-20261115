import YM.SatinExist.Secant
set_option autoImplicit false
set_option maxHeartbeats 330000
noncomputable section
namespace YM.CF.Buffered.Ballad
open Function Filter Metric Fock Mir.Trip Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye Emu Onyx Kea Flare Dial
open Cache Glaze
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology Kronecker
attribute [local instance] opCStarAlgebra
open Py.Rate.LocalLimit.Papal (Weaver household)
open YM.CF.Lamour YM.CF.Velvet YM.CF.Lamour.Bridge.Celeste
open Twah
namespace Chalice
/-! Adaptation of CFP SPF's uniform tangent proof. Now *matrices of generation*! also on-site hops, actual permit. -/
open Lamour.Bridge
open YM.Stationary (Gaia)
variable {N:Side} {R:ℕ} (s:Stone) (a:Cover) {I:Type*}
lemma ripe : Wort a s R N (1,1)= ∑ i∈modes s.1, ton ((pitcher a s.2).chargeF (R:=R) (setRuby s.1 i) true)*ton ((pitcher a s.2).chargeF (R:=R) i false):=by
 rw [words,smul_sum]; apply sum_congr rfl; intro i h; rw [in_lo,in_hi,Matrix.smul_mul,Matrix.mul_smul,smul_smul,neg_mul, show star (gain R)*gain R=(R:ℂ)^3 from ?_]; · rfl
 simp only [gain,Complex.star_def,Complex.conj_ofReal]; norm_cast; rw [← sq,Real.sq_sqrt (by positivity)]
variable (Z:I→Stone) (O:I → Cover)(L:List I)
def outfitC (i:I):Twah:= pitcher (O i) (Z i).2
abbrev wordsC (R:ℕ) : Weaver:= (L.map fun x:I=> Wort (O x) (Z x) R).prod
lemma pressC : Voice (wordsC Z O L R) (paper (L.map (outfitC Z O))):=by
 induction L with|nil=> exact Voice.one _|cons i l h=> have he:= Chalice.audience (O i) (Z i) R; rw [←cupArea (O i) (Z i).2] at he; exact he.mul h
abbrev gang (Z: I→Stone)(A:List (Stamp I))(i:I)(v:Slot): List (Stamp I):= A++[(i,setRuby (Z i).1 v,true),(i,v,false)]
-- price
local notation "Π*"=> List (Stamp I)
def prose (F:(List (Stamp I))→ℂ) (A:List (Stamp I)):List I→ℂ
| []=>F A
| i::l=> ∑ v∈modes (Z i).1, prose F (gang Z A i v) l
local notation "Ω*" => Twah.pulse (outfitC Z O) N R
variable {j:ℕ}
lemma wickHit (p:1≤ j)(u:Kea.Pad j N)(T:Jill.Male)(x:Wave (Single N))(v:Sea (spar j T (1: Pane N)) x)(g:List (Twah.Stamp I)):
 alleyR (mateK N) x (rollC (ton ∘ pulse (outfitC Z O) N R) g * wordsC Z O L R N (1,1)) = prose Z (runes (fun a b=> rankG (lake N j T) ((Ω*) a) ((Ω*) b))) g L:=by
 induction L generalizing g with
 | nil=> exact Twah.bank_chant (Y:=outfitC Z O) (fun i=>(Z i).1.1) ([]:List I) p u T x v g
 | cons i l h=>
    let G:= rollC (ton ∘ pulse (outfitC Z O) N R) g; let D:= wordsC Z O l R N (1,1); change alleyR _ x (G*(Wort (O i) (Z i) _ N (1,1)* D))=_; rw [ripe,sum_mul,mul_sum,map_sum]; refine sum_congr rfl fun t _=> ?_; rw [← h]
    apply congrArg (alleyR (mateK N) x); rw [show rollC (ton ∘ pulse (outfitC Z O) N R) (gang Z g i t)= G * (ton (((Ω*) (i,setRuby (Z i).1 t,true))) * ton ((Ω*) (i,t,false))) by unfold G; simp only [rollC,gang,List.map_append,List.prod_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]; rfl]; exact (mul_assoc ..).symm
-- tangent on all onsite systems
variable (sR:ℕ→ℕ)(Y:ℕ→ I → Cover){Q:ℕ→Side} (D:I→Gaia)
local notation "F" k:max => (outfitC Z (Y k))
abbrev digs (D:I→Gaia) : Twah.Cellz I→Gaia:= D ∘ Prod.fst
abbrev paint : I→DirSpin:= Prod.snd ∘ Z
abbrev depictionC :ℂ := Chalice.prose Z (runes (germRho (digs D) (paint Z))) [] L
lemma logicC : Twah.nearPoints R (outfitC Z O) = digs (fun i:I=> riseX (R:ℝ) (O i)):= by funext i; obtain ⟨i,b⟩:=i; cases b<;>rfl
variable (h: ∀ i, Tendsto (fun n:ℕ=>riseX (sR n:ℝ) (Y n i)) atTop (𝓝 (D i)))(p:∀ i j,D i=D j→ ∀ᶠ n in atTop,Y n i=Y n j)
include h p
lemma staves : Twah.riseUp (fun n=>F n) sR (digs D)∧ Twah.plateau (fun n=>F n) (digs D):=by
 constructor
 · intro i; simp_rw [logicC]; exact h i.1
 intro i j; rcases i with ⟨i,b⟩; rcases j with ⟨j,c⟩; cases b <;> cases c <;> exact p i j
omit h p
lemma scriptL (W:(List (Stamp I))→ℂ)(C:ℕ → List (Stamp I)→ℂ)(u:∀ i,Tendsto (fun n=> C n i) atTop (𝓝 (W i))) (K:List (Stamp I)): Tendsto (fun i=> prose Z (C i) K L) atTop (𝓝 (prose Z W K L)):=by induction L generalizing K with | nil=> exact u _| cons _ _ r=> exact tendsto_finsetSum _ (fun i _=>r _)
include h p
lemma tangentC' (j:ℕ)(Yh:Yard Q (fun i=>(sR i:ℝ)))(t:1≤j)(M:ℕ→Jill.Male)(Ht:∀ i,Kea.Pad j (Q i))(z:∀ i,Wave (Single (Q i)))(v:∀ i,Sea (spar j (M i) (1:Pane (Q i))) (z i)) : Tendsto (fun i:ℕ=> alleyR (mateK (Q i)) (z i) (wordsC Z (Y i) L (sR i) (Q i) (1,1))) atTop (𝓝 (depictionC Z L D)):=by
 obtain ⟨Yp,Yu⟩:=staves Z sR Y D h p
 let Z':=paint Z
 let Y':ℕ→I→Twah:=fun n=>F n
 let P': Plot (Stamp I) (fun i:ℕ=> (sR i:ℝ)):= ⟨fun i p=> crumbs Y' i (colbase p),pilotS Z',(digs D) ∘ colbase,fun x=> Yp _,fun x y=> Yu _ _⟩
 obtain ⟨u,p,g⟩:= lake_formal t
 have he(i:ℕ)(x:Stamp I):P'.tag (m:=i) 0 (Kea.tax emptyC) 1 x=pulse (Y' i) (Q i) (sR i) x:=by
    change nac _ _ _ _ _=nac _ _ _ _ _; rw [clear_canvas]; obtain ⟨x,p,b⟩:=x; cases b<;>rfl
 simp_rw [show ∀ i, alleyR (mateK (Q i)) (z i) (wordsC Z (Y i) L (sR i) (Q i) (1,1))=_ from (fun i:ℕ=> by simpa only [rollC,List.map_nil,List.prod_nil, one_mul] using (wickHit (R:=sR i) Z (Y i) L t (Ht i) (M i) _ (v i) []))];
 apply scriptL Z L _ _ ?_; intro x
 refine (P'.sun (r:=u) (C:=1) (d:=fun _=>emptyC) (fun i=>too _) M (fun i:ℕ=>lakeP _ j (M i)) (fun _=>0) Yh p (by norm_num) (fun x:Slot=> Eventually.of_forall (fun i=> g _ (Ht i).1 (M i) x)) t (fun _=>1) x).congr fun i=> ?_
 simp_rw [show ∀ (w:Stamp I), P'.tag (m:=i) _ _ _ w=pulse (Y' i) _ _ _ from he i]; rfl
omit h p
end Chalice
end YM.CF.Buffered.Ballad
