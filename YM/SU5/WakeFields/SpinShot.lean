import YM.SU5.Hiro.Morsel
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Hiro
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Lifted Bilinear Window Skye Emu Onyx Kea Flare Dial
open Cache Glaze
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open YM.CF.Lamour YM.CF.Velvet
open YM.CF.Lamour.Bridge.Celeste
open YM.CF.Py.Rate.LocalLimit.Papal (Weaver household)
open Ballad
open Twah (DirSpin)
-- Onyx self contract allowed iff exactly coincident. Transcript factor 2^3 (Gauge ruler). Public factorial.
namespace Crossing
open YM.Stationary (Gaia)
variable {s:ℕ→Side}{r:ℕ→ℕ}{U V:ℕ→ Cover}{M:ℕ→Jill.Male} {j:ℕ} (L G:DirSpin){X:Gaia}(u:Tendsto (fun i=> riseX (r i) (U i-V i)) atTop (𝓝 X)) (e:X=0→∀ᶠ i in atTop,U i=V i)
variable (W:Yard s (fun i=> (r i:ℝ))) (p:1 ≤ j)
include p W u e
lemma all_roll_shot : Tendsto (fun i=>dietary (r i) (U i) (V i) L G (s i) j (M i)) atTop (𝓝 (shotL X L G)):=by
 simp_rw [dietary,in_transcript]; let i:=sourceSlot; obtain ⟨c,hv,hT⟩:=lake_formal p
 have ht:=Emu.tally (L:=fun i=> (r i:ℝ)) (fun i=>too _) M (fun i=> lakeP _ j (M i)) (fun i=>0) W hv (by norm_num : (0:ℝ)<1) (fun x:Slot=>Eventually.of_forall fun i=>hT _ (W.even i) _ x) (alignedα L i) (alignedβ G i) U V X (by tauto) u p (fun _=>1)
 rw [show frank (alignedα L i) (alignedβ G i) X=shotL X L G from if_pos rfl] at ht; exact ht
omit p W u e
variable (j)
theorem whole_feast {X:Gaia}(w:1≤j)(r:ℕ→ℕ)(Q:Tendsto r atTop atTop)(W:∀ i,0<r i)(V U:ℕ→ Cover)(u:Tendsto (fun i=> riseX (r i) (U i-V i)) atTop (𝓝 X))(e:X=0→∀ᶠ i in atTop,U i=V i)(a:ℝ)(η:0<a): ∀ᶠ i in atTop,∀ᶠ N:Side in atTop,Even N.val → ∀ M:Jill.Male, dist (dietary (r i) (U i) (V i) L G N j M) (shotL X L G) ≤ a:=by
 by_contra h; obtain ⟨f,t,z⟩:= extraction_of_frequently_atTop (not_eventually.mp h)
 let Qu (i:ℕ):=r (f i); have ht(i:ℕ):0<(Qu i:ℝ):=by unfold Qu; exact_mod_cast W (f i)
 choose Y m v p h using fun i=> (show ∃ (N:Side)(M:Jill.Male), Even N.val∧(Qu i:ℝ)*Ember.pinch N≤ (2:ℝ)⁻¹^i∧ ¬ dist (dietary (r (f i)) (U (f i)) (V (f i)) L G N j M) (shotL X L G)≤ a from by
   obtain ⟨k,v⟩:=Glaze.pick_depth (p:=(show 0<(2:ℝ)⁻¹^i/(Qu i:ℝ) from (by have e:= ht i; positivity)))
   have he:=z i; replace he :=not_eventually.mp he; obtain ⟨N,h,vN⟩:= (he.and_eventually (eventually_ge_atTop (⟨k+1,by omega⟩:Side))).exists; -- remove
   push Not at h; obtain ⟨H,M,g⟩:=h; exact ⟨N,M,H, (mul_comm _ _).le.trans ((le_div_iff₀ (ht i)).1 (v (by change k+1 ≤ N.val at vN; omega))),g.not_ge⟩)
 let Q:= Q.comp t.tendsto_atTop; let d:= u.comp t.tendsto_atTop
 have hx: Yard Y (fun i=> (Qu i:ℝ)):= ⟨ht, tendsto_natCast_atTop_atTop.comp Q,squeeze_zero (fun i=> mul_nonneg (ht i).le (Ember.pinch_pos _).le) p (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)),v⟩
 let A:= U ∘ f; let B:= V ∘ f
 have he:Tendsto (fun i=>dietary (r (f i)) (U (f i)) (V (f i)) L G (Y i) j (m i)) atTop (𝓝 (shotL X L G)):= all_roll_shot (M:=m) (U:=A) (V:=B) L G d (fun h=> t.tendsto_atTop.eventually (e h)) hx w
 obtain ⟨i,f⟩:= (Metric.tendsto_nhds.mp he a η).exists; exact h _ f.le

lemma lodge_scale (N:Side) (j:ℕ) (M:Jill.Male) (U V:Cover)(L G:DirSpin)(r:ℕ) :
 dietary r U V L G N j M=(r:ℂ)^3*dietary 1 U V L G N j M := by
 unfold dietary; simp_rw [in_transcript, Emu.hopF]; push_cast; ring

-- convenience for roll of en0/ex0.
variable {J:Type*} {N:Side} (U:J→ Cover) (s:J→ DirSpin) (R:ℕ)
abbrev Story (J : Type*) := List (Twah.Stamp J)
abbrev cove (I: J → Cover) (s:J→DirSpin) := fun (x:J)=> unifyT (I x) (s x)
abbrev rack (N:Side) := Twah.pulse (cove U s) N R
abbrev covRead (j:ℕ) (r:ℕ) (U:J→ Cover)(s:J→ DirSpin) (N:Side)(M:Jill.Male) := fun i k=>rankG (lake N j M) (rack U s r N i) (rack U s r N k)

lemma chosen {M:Jill.Male} (p:1≤j)(w:Kea.Pad j N)(h:Wave (Single N))(q:Sea (spar j M (1:Pane N)) h)
    (L:List (Twah.Stamp J)) : alleyR (mateK N) h (rollC (ton∘rack U s R N) L)=Emu.runes (covRead j R U s N M) L:=by
 let Z(_ : J):Lead.Clan:= Classical.arbitrary _ -- ambiguity `Z`
 have hv:=Twah.bank_chant (R:=R) (cove U s) Z [] p w M h q L; rw [show Twah.plait _ _ _ _ _ _=(1:FC (Single N)) from (show Twah.plait (cove U s) Z [] R N (1,1)=1 from rfl),mul_one] at hv; exact hv

-- κ actor coefficient on Wick L proof, lifted version of private SpinReceipt. Expose.
variable {α β: Type*}
lemma howPair {L:List α} (z:Bout α)(h:z∈picks L): z.back.length+1=L.length:=by
 induction L generalizing z with
 | nil=> simp [picks] at h
 | cons x L ih=>
    rcases List.mem_cons.mp h with p|p; · rw [p]; rfl
    obtain ⟨x,h',rfl⟩:= List.mem_map.mp p; exact congrArg (·+1) (ih x h') 
lemma howMuch {L:List α} (v:Cl α)(h:v∈ claps L): v.up.length*2+v.term.length=L.length:=by
 induction L generalizing v with
 | nil=> change v∈[⟨false, [],[]⟩] at h; rw [List.mem_singleton.mp h]; rfl
 | cons i L ih=>
    obtain ⟨l,q,p⟩:= List.mem_flatMap.mp h; specialize ih l q; rcases List.mem_cons.mp p with p|p
    · rw [p]; change l.up.length*2+(l.term.length+1)=L.length+1; omega
    obtain ⟨y,p',rfl⟩:= List.mem_map.mp p; change (l.up.length+1)*2+y.back.length=L.length+1; have hp:=howPair y p'; omega
lemma offer_factor {L:List α} (z:Cl α)(D:α→α→ℂ)(a:ℂ)(h:z∈claps L) (M:ℕ)(p:L.length=M*2) : spinC (fun u v=>a*D u v) z= a^M * spinC D z:=by
 let d(u v:α):= a*D u v; unfold spinC; split; swap; · rw [mul_zero]
 next he=> have ht:=howMuch z h; rw [List.isEmpty_iff_length_eq_zero] at he; rw [he,p] at ht; have hz:z.up.length=M:=by omega
           have hf(V:List (α×α)) : (V.map (fun u=>a* D u.1 u.2)).prod=a^V.length*(V.map (fun u=>D u.1 u.2)).prod:=by induction V with|nil=> simp|cons z v ih=>rw [List.map_cons,List.map_cons,List.prod_cons,List.prod_cons,ih,List.length_cons,pow_succ]; ring -- indent
           unfold offer; rw [hf,hz]; ring
lemma rune_factor (L:List α)(M:ℕ)(p:L.length=M*2)(D:α→α→ℂ)(a:ℂ): runes (fun u v=>a*D u v) L=a^M*runes D L:=by
 unfold runes; generalize e : claps L= W; have he:∀ z∈ W,z∈ claps L:= by rw [e]; tauto; -- tune
 clear e; induction W with|nil=>simp|cons i W ih=> rw [List.map_cons,List.map_cons,List.sum_cons,List.sum_cons,ih (fun i p=> he i (List.mem_cons_of_mem _ p)),offer_factor i D a (he i (List.mem_cons_self)) M p,mul_add]

lemma rune_ride (X:Filter β) (G:α→α→ℂ)(F:β→α→α→ℂ)(h:∀ i j,Tendsto (fun m=>F m i j) X (𝓝 (G i j)))(L: List α): Tendsto (fun m=>runes (F m) L) X (𝓝 (runes G L)):=by
 have he(W: List (α × α)):Tendsto (fun i=> (W.map fun v=> F i v.1 v.2).prod) X (𝓝 ((W.map fun v=> G v.1 v.2).prod)):=by
   induction W with| nil=> exact tendsto_const_nhds| cons i t ih=> exact (h i.1 i.2).mul ih
 have hp(W:Cl α) : Tendsto (fun i=>spinC (F i) W) X (𝓝 (spinC G W)):=by
   unfold spinC; split_ifs; exact (he _).const_mul _; exact tendsto_const_nhds -- tune
 unfold runes; generalize claps L=W; induction W with| nil=>exact tendsto_const_nhds| cons a l ih=> exact (hp a).add ih
#print axioms chosen
#print axioms whole_feast
#print axioms rune_factor
#print axioms lodge_scale
#print axioms rune_ride
end Crossing
end YM.CF.Hiro
