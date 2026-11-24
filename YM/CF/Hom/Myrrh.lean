import YM.CF.Hom.Barn
import YM.Next.FREE_KERNELS.Calendar
import YM.LocalH.Haar
set_option autoImplicit false
noncomputable section
namespace YM.CF.Hom
open Function Filter NormedSpace Lattice Laurent Bloch Wilson Precision RG Work Exterior Next.Free Work.F08 Craft Pressure
open scoped Topology BigOperators Matrix
variable {j:ℕ}{K:KernelChoices}{p q:Clip}{η a C:ℝ}{n:ℕ}{G:Gauge}
open Bid
structure Paddle(T:Flight j j)(K:KernelChoices)(X Y:Bed)(p:Clip)(R:Towers T.L)(r A:ℝ) :Prop where
 first: R.A0=(T.duo K.penalty).A0
 pay: R.Deep r A (j-2)
 roll {c f:Side}(hc:f.val=c.val*T.L.val): Towers.Roll (T.visit K hc) X Y R p p
 link {c f:Side}(hc:f.val=c.val*T.L.val): Towers.Diagonal (T.visit K hc) X Y R
lemma packageK (x:0<a)(he:0<η) (p:Clip)(hj:4≤j) (C':ℝ) :∃ z W:ℝ,0<z ∧0<W∧W≥C'∧ z≤a ∧ ∀ q: Clip,q.direct=p.direct→∀ f: Flight j j,n≤f.L.val→∀ u v:ℝ, 0≤u → 0≤v→HopQuote K j j u v a η C n→∀ X Y:Bed,MainIn G q X η a C → MainIn G q Y η a C → Defined K.penalty u f.wing X→Defined K.penalty v f.land Y→∃ P:Towers f.L, Paddle f K X Y q P z W:=by
 obtain ⟨w,B,c,hp,hC,H⟩:= Work.F07.answer (TypeFace 3) C η a he x
 obtain ⟨γ,M,hw,T⟩:= Work.F08.answer p p K.penalty C a a C c B (j-2) K.penalty_pos x x hC
 let z:= min γ a; let U:=max (max M C') 1; have hx: γ≥z:=min_le_left ..; have hU: M≤U:=(le_max_left ..).trans (le_max_left ..)
 refine ⟨z,U,lt_min hw x,lt_of_lt_of_le zero_lt_one (le_max_right ..),(le_max_right ..).trans (le_max_left ..),min_le_right ..,fun q k f hf u v hy hz R X Y W V G T'=>?_⟩
 obtain ⟨A,g,h⟩:= R f; obtain ⟨Q,hq,r,hv⟩:= H _ g (h hf); obtain ⟨P,E,D⟩:= T X Y W.1 V.1 Q r f.L f.odd _ A
 have y{c g: Side}(e:g.val=c.val*f.L.val): Replaces (f.visitRatio e) X Y p p K.penalty Q (f.duo K.penalty) P:= D c g e
 let g: ℕ:= f.L.val; let s:= y (c:=1) (g:=f.L) (by change g=1*g; omega)
 have he:E=E:=rfl; refine ⟨P,s.first.symm,?_,fun {c f₁} e=>?_,fun {c f₁} e=>?_⟩
 · obtain ⟨h,g,p,q⟩:= E; exact ⟨fun i j=> (h i j).mono hx hU, fun i j=>(g i j).mono hx hU, fun i j=>(p i j).mono hx (div_le_div_of_nonneg_right hU (by positivity)), fun l hl=> ⟨strip_mono (q l hl).1 hx (div_le_div_of_nonneg_right hU (by positivity)), strip_mono (q l hl).2 hx (div_le_div_of_nonneg_right hU (by positivity))⟩⟩ -- tune cross_strip
 · let S:= f.visit K e; apply roll_direct k.symm k.symm (S:=S) (X:=X) (Y:=Y)
   apply Work.F09.answer _ _ S (f.duo _) P X Y Q (f.rollFunds K.penalty u v) p p η C η C (y e) (floor_direct k (W.2.1 _)) (floor_direct k (V.2.1 _)) (Next.Free.diagonal K v u hz hy f hj X Y G T' e) (fun n=>(hv n).1) (check_bleep K v u hz hy f hj X Y G T' e)
 obtain ⟨h1,h2,h3⟩:= Next.Free.diagonal K v u hz hy f hj X Y G T' e; constructor
 · rw [←s.first]; exact h1
 · rw [←s.form]; exact h2
 rw [←s.form, ←s.first]; exact h3
end YM.CF.Hom
