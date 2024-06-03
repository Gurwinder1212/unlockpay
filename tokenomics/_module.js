function noop() { }
const identity = x => x;
function assign(tar, src) {
    // @ts-ignore
    for (const k in src)
        tar[k] = src[k];
    return tar;
}
function run(fn) {
    return fn();
}
function blank_object() {
    return Object.create(null);
}
function run_all(fns) {
    fns.forEach(run);
}
function is_function(thing) {
    return typeof thing === 'function';
}
function safe_not_equal(a, b) {
    return a != a ? b == b : a !== b || ((a && typeof a === 'object') || typeof a === 'function');
}
let src_url_equal_anchor;
function src_url_equal(element_src, url) {
    if (!src_url_equal_anchor) {
        src_url_equal_anchor = document.createElement('a');
    }
    src_url_equal_anchor.href = url;
    return element_src === src_url_equal_anchor.href;
}
function is_empty(obj) {
    return Object.keys(obj).length === 0;
}
function exclude_internal_props(props) {
    const result = {};
    for (const k in props)
        if (k[0] !== '$')
            result[k] = props[k];
    return result;
}
function null_to_empty(value) {
    return value == null ? '' : value;
}

const is_client = typeof window !== 'undefined';
let now = is_client
    ? () => window.performance.now()
    : () => Date.now();
let raf = is_client ? cb => requestAnimationFrame(cb) : noop;

const tasks = new Set();
function run_tasks(now) {
    tasks.forEach(task => {
        if (!task.c(now)) {
            tasks.delete(task);
            task.f();
        }
    });
    if (tasks.size !== 0)
        raf(run_tasks);
}
/**
 * Creates a new task that runs on each raf frame
 * until it returns a falsy value or is aborted
 */
function loop(callback) {
    let task;
    if (tasks.size === 0)
        raf(run_tasks);
    return {
        promise: new Promise(fulfill => {
            tasks.add(task = { c: callback, f: fulfill });
        }),
        abort() {
            tasks.delete(task);
        }
    };
}

// Track which nodes are claimed during hydration. Unclaimed nodes can then be removed from the DOM
// at the end of hydration without touching the remaining nodes.
let is_hydrating = false;
function start_hydrating() {
    is_hydrating = true;
}
function end_hydrating() {
    is_hydrating = false;
}
function upper_bound(low, high, key, value) {
    // Return first index of value larger than input value in the range [low, high)
    while (low < high) {
        const mid = low + ((high - low) >> 1);
        if (key(mid) <= value) {
            low = mid + 1;
        }
        else {
            high = mid;
        }
    }
    return low;
}
function init_hydrate(target) {
    if (target.hydrate_init)
        return;
    target.hydrate_init = true;
    // We know that all children have claim_order values since the unclaimed have been detached if target is not <head>
    let children = target.childNodes;
    // If target is <head>, there may be children without claim_order
    if (target.nodeName === 'HEAD') {
        const myChildren = [];
        for (let i = 0; i < children.length; i++) {
            const node = children[i];
            if (node.claim_order !== undefined) {
                myChildren.push(node);
            }
        }
        children = myChildren;
    }
    /*
    * Reorder claimed children optimally.
    * We can reorder claimed children optimally by finding the longest subsequence of
    * nodes that are already claimed in order and only moving the rest. The longest
    * subsequence of nodes that are claimed in order can be found by
    * computing the longest increasing subsequence of .claim_order values.
    *
    * This algorithm is optimal in generating the least amount of reorder operations
    * possible.
    *
    * Proof:
    * We know that, given a set of reordering operations, the nodes that do not move
    * always form an increasing subsequence, since they do not move among each other
    * meaning that they must be already ordered among each other. Thus, the maximal
    * set of nodes that do not move form a longest increasing subsequence.
    */
    // Compute longest increasing subsequence
    // m: subsequence length j => index k of smallest value that ends an increasing subsequence of length j
    const m = new Int32Array(children.length + 1);
    // Predecessor indices + 1
    const p = new Int32Array(children.length);
    m[0] = -1;
    let longest = 0;
    for (let i = 0; i < children.length; i++) {
        const current = children[i].claim_order;
        // Find the largest subsequence length such that it ends in a value less than our current value
        // upper_bound returns first greater value, so we subtract one
        // with fast path for when we are on the current longest subsequence
        const seqLen = ((longest > 0 && children[m[longest]].claim_order <= current) ? longest + 1 : upper_bound(1, longest, idx => children[m[idx]].claim_order, current)) - 1;
        p[i] = m[seqLen] + 1;
        const newLen = seqLen + 1;
        // We can guarantee that current is the smallest value. Otherwise, we would have generated a longer sequence.
        m[newLen] = i;
        longest = Math.max(newLen, longest);
    }
    // The longest increasing subsequence of nodes (initially reversed)
    const lis = [];
    // The rest of the nodes, nodes that will be moved
    const toMove = [];
    let last = children.length - 1;
    for (let cur = m[longest] + 1; cur != 0; cur = p[cur - 1]) {
        lis.push(children[cur - 1]);
        for (; last >= cur; last--) {
            toMove.push(children[last]);
        }
        last--;
    }
    for (; last >= 0; last--) {
        toMove.push(children[last]);
    }
    lis.reverse();
    // We sort the nodes being moved to guarantee that their insertion order matches the claim order
    toMove.sort((a, b) => a.claim_order - b.claim_order);
    // Finally, we move the nodes
    for (let i = 0, j = 0; i < toMove.length; i++) {
        while (j < lis.length && toMove[i].claim_order >= lis[j].claim_order) {
            j++;
        }
        const anchor = j < lis.length ? lis[j] : null;
        target.insertBefore(toMove[i], anchor);
    }
}
function append(target, node) {
    target.appendChild(node);
}
function get_root_for_style(node) {
    if (!node)
        return document;
    const root = node.getRootNode ? node.getRootNode() : node.ownerDocument;
    if (root && root.host) {
        return root;
    }
    return node.ownerDocument;
}
function append_empty_stylesheet(node) {
    const style_element = element('style');
    append_stylesheet(get_root_for_style(node), style_element);
    return style_element.sheet;
}
function append_stylesheet(node, style) {
    append(node.head || node, style);
    return style.sheet;
}
function append_hydration(target, node) {
    if (is_hydrating) {
        init_hydrate(target);
        if ((target.actual_end_child === undefined) || ((target.actual_end_child !== null) && (target.actual_end_child.parentNode !== target))) {
            target.actual_end_child = target.firstChild;
        }
        // Skip nodes of undefined ordering
        while ((target.actual_end_child !== null) && (target.actual_end_child.claim_order === undefined)) {
            target.actual_end_child = target.actual_end_child.nextSibling;
        }
        if (node !== target.actual_end_child) {
            // We only insert if the ordering of this node should be modified or the parent node is not target
            if (node.claim_order !== undefined || node.parentNode !== target) {
                target.insertBefore(node, target.actual_end_child);
            }
        }
        else {
            target.actual_end_child = node.nextSibling;
        }
    }
    else if (node.parentNode !== target || node.nextSibling !== null) {
        target.appendChild(node);
    }
}
function insert_hydration(target, node, anchor) {
    if (is_hydrating && !anchor) {
        append_hydration(target, node);
    }
    else if (node.parentNode !== target || node.nextSibling != anchor) {
        target.insertBefore(node, anchor || null);
    }
}
function detach(node) {
    if (node.parentNode) {
        node.parentNode.removeChild(node);
    }
}
function destroy_each(iterations, detaching) {
    for (let i = 0; i < iterations.length; i += 1) {
        if (iterations[i])
            iterations[i].d(detaching);
    }
}
function element(name) {
    return document.createElement(name);
}
function svg_element(name) {
    return document.createElementNS('http://www.w3.org/2000/svg', name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
}
function empty() {
    return text('');
}
function listen(node, event, handler, options) {
    node.addEventListener(event, handler, options);
    return () => node.removeEventListener(event, handler, options);
}
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
}
/**
 * List of attributes that should always be set through the attr method,
 * because updating them through the property setter doesn't work reliably.
 * In the example of `width`/`height`, the problem is that the setter only
 * accepts numeric values, but the attribute can also be set to a string like `50%`.
 * If this list becomes too big, rethink this approach.
 */
const always_set_through_set_attribute = ['width', 'height'];
function set_attributes(node, attributes) {
    // @ts-ignore
    const descriptors = Object.getOwnPropertyDescriptors(node.__proto__);
    for (const key in attributes) {
        if (attributes[key] == null) {
            node.removeAttribute(key);
        }
        else if (key === 'style') {
            node.style.cssText = attributes[key];
        }
        else if (key === '__value') {
            node.value = node[key] = attributes[key];
        }
        else if (descriptors[key] && descriptors[key].set && always_set_through_set_attribute.indexOf(key) === -1) {
            node[key] = attributes[key];
        }
        else {
            attr(node, key, attributes[key]);
        }
    }
}
function set_svg_attributes(node, attributes) {
    for (const key in attributes) {
        attr(node, key, attributes[key]);
    }
}
function set_custom_element_data(node, prop, value) {
    if (prop in node) {
        node[prop] = typeof node[prop] === 'boolean' && value === '' ? true : value;
    }
    else {
        attr(node, prop, value);
    }
}
function children(element) {
    return Array.from(element.childNodes);
}
function init_claim_info(nodes) {
    if (nodes.claim_info === undefined) {
        nodes.claim_info = { last_index: 0, total_claimed: 0 };
    }
}
function claim_node(nodes, predicate, processNode, createNode, dontUpdateLastIndex = false) {
    // Try to find nodes in an order such that we lengthen the longest increasing subsequence
    init_claim_info(nodes);
    const resultNode = (() => {
        // We first try to find an element after the previous one
        for (let i = nodes.claim_info.last_index; i < nodes.length; i++) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                return node;
            }
        }
        // Otherwise, we try to find one before
        // We iterate in reverse so that we don't go too far back
        for (let i = nodes.claim_info.last_index - 1; i >= 0; i--) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                else if (replacement === undefined) {
                    // Since we spliced before the last_index, we decrease it
                    nodes.claim_info.last_index--;
                }
                return node;
            }
        }
        // If we can't find any matching node, we create a new one
        return createNode();
    })();
    resultNode.claim_order = nodes.claim_info.total_claimed;
    nodes.claim_info.total_claimed += 1;
    return resultNode;
}
function claim_element_base(nodes, name, attributes, create_element) {
    return claim_node(nodes, (node) => node.nodeName === name, (node) => {
        const remove = [];
        for (let j = 0; j < node.attributes.length; j++) {
            const attribute = node.attributes[j];
            if (!attributes[attribute.name]) {
                remove.push(attribute.name);
            }
        }
        remove.forEach(v => node.removeAttribute(v));
        return undefined;
    }, () => create_element(name));
}
function claim_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, element);
}
function claim_svg_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, svg_element);
}
function claim_text(nodes, data) {
    return claim_node(nodes, (node) => node.nodeType === 3, (node) => {
        const dataStr = '' + data;
        if (node.data.startsWith(dataStr)) {
            if (node.data.length !== dataStr.length) {
                return node.splitText(dataStr.length);
            }
        }
        else {
            node.data = dataStr;
        }
    }, () => text(data), true // Text nodes should not update last index since it is likely not worth it to eliminate an increasing subsequence of actual elements
    );
}
function claim_space(nodes) {
    return claim_text(nodes, ' ');
}
function set_data(text, data) {
    data = '' + data;
    if (text.data === data)
        return;
    text.data = data;
}
function set_style(node, key, value, important) {
    if (value == null) {
        node.style.removeProperty(key);
    }
    else {
        node.style.setProperty(key, value, important ? 'important' : '');
    }
}
function custom_event(type, detail, { bubbles = false, cancelable = false } = {}) {
    const e = document.createEvent('CustomEvent');
    e.initCustomEvent(type, bubbles, cancelable, detail);
    return e;
}
function head_selector(nodeId, head) {
    const result = [];
    let started = 0;
    for (const node of head.childNodes) {
        if (node.nodeType === 8 /* comment node */) {
            const comment = node.textContent.trim();
            if (comment === `HEAD_${nodeId}_END`) {
                started -= 1;
                result.push(node);
            }
            else if (comment === `HEAD_${nodeId}_START`) {
                started += 1;
                result.push(node);
            }
        }
        else if (started > 0) {
            result.push(node);
        }
    }
    return result;
}

// we need to store the information for multiple documents because a Svelte application could also contain iframes
// https://github.com/sveltejs/svelte/issues/3624
const managed_styles = new Map();
let active = 0;
// https://github.com/darkskyapp/string-hash/blob/master/index.js
function hash(str) {
    let hash = 5381;
    let i = str.length;
    while (i--)
        hash = ((hash << 5) - hash) ^ str.charCodeAt(i);
    return hash >>> 0;
}
function create_style_information(doc, node) {
    const info = { stylesheet: append_empty_stylesheet(node), rules: {} };
    managed_styles.set(doc, info);
    return info;
}
function create_rule(node, a, b, duration, delay, ease, fn, uid = 0) {
    const step = 16.666 / duration;
    let keyframes = '{\n';
    for (let p = 0; p <= 1; p += step) {
        const t = a + (b - a) * ease(p);
        keyframes += p * 100 + `%{${fn(t, 1 - t)}}\n`;
    }
    const rule = keyframes + `100% {${fn(b, 1 - b)}}\n}`;
    const name = `__svelte_${hash(rule)}_${uid}`;
    const doc = get_root_for_style(node);
    const { stylesheet, rules } = managed_styles.get(doc) || create_style_information(doc, node);
    if (!rules[name]) {
        rules[name] = true;
        stylesheet.insertRule(`@keyframes ${name} ${rule}`, stylesheet.cssRules.length);
    }
    const animation = node.style.animation || '';
    node.style.animation = `${animation ? `${animation}, ` : ''}${name} ${duration}ms linear ${delay}ms 1 both`;
    active += 1;
    return name;
}
function delete_rule(node, name) {
    const previous = (node.style.animation || '').split(', ');
    const next = previous.filter(name
        ? anim => anim.indexOf(name) < 0 // remove specific animation
        : anim => anim.indexOf('__svelte') === -1 // remove all Svelte animations
    );
    const deleted = previous.length - next.length;
    if (deleted) {
        node.style.animation = next.join(', ');
        active -= deleted;
        if (!active)
            clear_rules();
    }
}
function clear_rules() {
    raf(() => {
        if (active)
            return;
        managed_styles.forEach(info => {
            const { ownerNode } = info.stylesheet;
            // there is no ownerNode if it runs on jsdom.
            if (ownerNode)
                detach(ownerNode);
        });
        managed_styles.clear();
    });
}

let current_component;
function set_current_component(component) {
    current_component = component;
}
function get_current_component() {
    if (!current_component)
        throw new Error('Function called outside component initialization');
    return current_component;
}
/**
 * The `onMount` function schedules a callback to run as soon as the component has been mounted to the DOM.
 * It must be called during the component's initialisation (but doesn't need to live *inside* the component;
 * it can be called from an external module).
 *
 * `onMount` does not run inside a [server-side component](/docs#run-time-server-side-component-api).
 *
 * https://svelte.dev/docs#run-time-svelte-onmount
 */
function onMount(fn) {
    get_current_component().$$.on_mount.push(fn);
}
/**
 * Schedules a callback to run immediately before the component is unmounted.
 *
 * Out of `onMount`, `beforeUpdate`, `afterUpdate` and `onDestroy`, this is the
 * only one that runs inside a server-side component.
 *
 * https://svelte.dev/docs#run-time-svelte-ondestroy
 */
function onDestroy(fn) {
    get_current_component().$$.on_destroy.push(fn);
}
/**
 * Creates an event dispatcher that can be used to dispatch [component events](/docs#template-syntax-component-directives-on-eventname).
 * Event dispatchers are functions that can take two arguments: `name` and `detail`.
 *
 * Component events created with `createEventDispatcher` create a
 * [CustomEvent](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent).
 * These events do not [bubble](https://developer.mozilla.org/en-US/docs/Learn/JavaScript/Building_blocks/Events#Event_bubbling_and_capture).
 * The `detail` argument corresponds to the [CustomEvent.detail](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent/detail)
 * property and can contain any type of data.
 *
 * https://svelte.dev/docs#run-time-svelte-createeventdispatcher
 */
function createEventDispatcher() {
    const component = get_current_component();
    return (type, detail, { cancelable = false } = {}) => {
        const callbacks = component.$$.callbacks[type];
        if (callbacks) {
            // TODO are there situations where events could be dispatched
            // in a server (non-DOM) environment?
            const event = custom_event(type, detail, { cancelable });
            callbacks.slice().forEach(fn => {
                fn.call(component, event);
            });
            return !event.defaultPrevented;
        }
        return true;
    };
}

const dirty_components = [];
const binding_callbacks = [];
let render_callbacks = [];
const flush_callbacks = [];
const resolved_promise = /* @__PURE__ */ Promise.resolve();
let update_scheduled = false;
function schedule_update() {
    if (!update_scheduled) {
        update_scheduled = true;
        resolved_promise.then(flush);
    }
}
function add_render_callback(fn) {
    render_callbacks.push(fn);
}
// flush() calls callbacks in this order:
// 1. All beforeUpdate callbacks, in order: parents before children
// 2. All bind:this callbacks, in reverse order: children before parents.
// 3. All afterUpdate callbacks, in order: parents before children. EXCEPT
//    for afterUpdates called during the initial onMount, which are called in
//    reverse order: children before parents.
// Since callbacks might update component values, which could trigger another
// call to flush(), the following steps guard against this:
// 1. During beforeUpdate, any updated components will be added to the
//    dirty_components array and will cause a reentrant call to flush(). Because
//    the flush index is kept outside the function, the reentrant call will pick
//    up where the earlier call left off and go through all dirty components. The
//    current_component value is saved and restored so that the reentrant call will
//    not interfere with the "parent" flush() call.
// 2. bind:this callbacks cannot trigger new flush() calls.
// 3. During afterUpdate, any updated components will NOT have their afterUpdate
//    callback called a second time; the seen_callbacks set, outside the flush()
//    function, guarantees this behavior.
const seen_callbacks = new Set();
let flushidx = 0; // Do *not* move this inside the flush() function
function flush() {
    // Do not reenter flush while dirty components are updated, as this can
    // result in an infinite loop. Instead, let the inner flush handle it.
    // Reentrancy is ok afterwards for bindings etc.
    if (flushidx !== 0) {
        return;
    }
    const saved_component = current_component;
    do {
        // first, call beforeUpdate functions
        // and update components
        try {
            while (flushidx < dirty_components.length) {
                const component = dirty_components[flushidx];
                flushidx++;
                set_current_component(component);
                update(component.$$);
            }
        }
        catch (e) {
            // reset dirty state to not end up in a deadlocked state and then rethrow
            dirty_components.length = 0;
            flushidx = 0;
            throw e;
        }
        set_current_component(null);
        dirty_components.length = 0;
        flushidx = 0;
        while (binding_callbacks.length)
            binding_callbacks.pop()();
        // then, once components are updated, call
        // afterUpdate functions. This may cause
        // subsequent updates...
        for (let i = 0; i < render_callbacks.length; i += 1) {
            const callback = render_callbacks[i];
            if (!seen_callbacks.has(callback)) {
                // ...so guard against infinite loops
                seen_callbacks.add(callback);
                callback();
            }
        }
        render_callbacks.length = 0;
    } while (dirty_components.length);
    while (flush_callbacks.length) {
        flush_callbacks.pop()();
    }
    update_scheduled = false;
    seen_callbacks.clear();
    set_current_component(saved_component);
}
function update($$) {
    if ($$.fragment !== null) {
        $$.update();
        run_all($$.before_update);
        const dirty = $$.dirty;
        $$.dirty = [-1];
        $$.fragment && $$.fragment.p($$.ctx, dirty);
        $$.after_update.forEach(add_render_callback);
    }
}
/**
 * Useful for example to execute remaining `afterUpdate` callbacks before executing `destroy`.
 */
function flush_render_callbacks(fns) {
    const filtered = [];
    const targets = [];
    render_callbacks.forEach((c) => fns.indexOf(c) === -1 ? filtered.push(c) : targets.push(c));
    targets.forEach((c) => c());
    render_callbacks = filtered;
}

let promise;
function wait() {
    if (!promise) {
        promise = Promise.resolve();
        promise.then(() => {
            promise = null;
        });
    }
    return promise;
}
function dispatch(node, direction, kind) {
    node.dispatchEvent(custom_event(`${direction ? 'intro' : 'outro'}${kind}`));
}
const outroing = new Set();
let outros;
function group_outros() {
    outros = {
        r: 0,
        c: [],
        p: outros // parent group
    };
}
function check_outros() {
    if (!outros.r) {
        run_all(outros.c);
    }
    outros = outros.p;
}
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
}
function transition_out(block, local, detach, callback) {
    if (block && block.o) {
        if (outroing.has(block))
            return;
        outroing.add(block);
        outros.c.push(() => {
            outroing.delete(block);
            if (callback) {
                if (detach)
                    block.d(1);
                callback();
            }
        });
        block.o(local);
    }
    else if (callback) {
        callback();
    }
}
const null_transition = { duration: 0 };
function create_bidirectional_transition(node, fn, params, intro) {
    const options = { direction: 'both' };
    let config = fn(node, params, options);
    let t = intro ? 0 : 1;
    let running_program = null;
    let pending_program = null;
    let animation_name = null;
    function clear_animation() {
        if (animation_name)
            delete_rule(node, animation_name);
    }
    function init(program, duration) {
        const d = (program.b - t);
        duration *= Math.abs(d);
        return {
            a: t,
            b: program.b,
            d,
            duration,
            start: program.start,
            end: program.start + duration,
            group: program.group
        };
    }
    function go(b) {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        const program = {
            start: now() + delay,
            b
        };
        if (!b) {
            // @ts-ignore todo: improve typings
            program.group = outros;
            outros.r += 1;
        }
        if (running_program || pending_program) {
            pending_program = program;
        }
        else {
            // if this is an intro, and there's a delay, we need to do
            // an initial tick and/or apply CSS animation immediately
            if (css) {
                clear_animation();
                animation_name = create_rule(node, t, b, duration, delay, easing, css);
            }
            if (b)
                tick(0, 1);
            running_program = init(program, duration);
            add_render_callback(() => dispatch(node, b, 'start'));
            loop(now => {
                if (pending_program && now > pending_program.start) {
                    running_program = init(pending_program, duration);
                    pending_program = null;
                    dispatch(node, running_program.b, 'start');
                    if (css) {
                        clear_animation();
                        animation_name = create_rule(node, t, running_program.b, running_program.duration, 0, easing, config.css);
                    }
                }
                if (running_program) {
                    if (now >= running_program.end) {
                        tick(t = running_program.b, 1 - t);
                        dispatch(node, running_program.b, 'end');
                        if (!pending_program) {
                            // we're done
                            if (running_program.b) {
                                // intro — we can tidy up immediately
                                clear_animation();
                            }
                            else {
                                // outro — needs to be coordinated
                                if (!--running_program.group.r)
                                    run_all(running_program.group.c);
                            }
                        }
                        running_program = null;
                    }
                    else if (now >= running_program.start) {
                        const p = now - running_program.start;
                        t = running_program.a + running_program.d * easing(p / running_program.duration);
                        tick(t, 1 - t);
                    }
                }
                return !!(running_program || pending_program);
            });
        }
    }
    return {
        run(b) {
            if (is_function(config)) {
                wait().then(() => {
                    // @ts-ignore
                    config = config(options);
                    go(b);
                });
            }
            else {
                go(b);
            }
        },
        end() {
            clear_animation();
            running_program = pending_program = null;
        }
    };
}

function get_spread_update(levels, updates) {
    const update = {};
    const to_null_out = {};
    const accounted_for = { $$scope: 1 };
    let i = levels.length;
    while (i--) {
        const o = levels[i];
        const n = updates[i];
        if (n) {
            for (const key in o) {
                if (!(key in n))
                    to_null_out[key] = 1;
            }
            for (const key in n) {
                if (!accounted_for[key]) {
                    update[key] = n[key];
                    accounted_for[key] = 1;
                }
            }
            levels[i] = n;
        }
        else {
            for (const key in o) {
                accounted_for[key] = 1;
            }
        }
    }
    for (const key in to_null_out) {
        if (!(key in update))
            update[key] = undefined;
    }
    return update;
}
function create_component(block) {
    block && block.c();
}
function claim_component(block, parent_nodes) {
    block && block.l(parent_nodes);
}
function mount_component(component, target, anchor, customElement) {
    const { fragment, after_update } = component.$$;
    fragment && fragment.m(target, anchor);
    if (!customElement) {
        // onMount happens before the initial afterUpdate
        add_render_callback(() => {
            const new_on_destroy = component.$$.on_mount.map(run).filter(is_function);
            // if the component was destroyed immediately
            // it will update the `$$.on_destroy` reference to `null`.
            // the destructured on_destroy may still reference to the old array
            if (component.$$.on_destroy) {
                component.$$.on_destroy.push(...new_on_destroy);
            }
            else {
                // Edge case - component was destroyed immediately,
                // most likely as a result of a binding initialising
                run_all(new_on_destroy);
            }
            component.$$.on_mount = [];
        });
    }
    after_update.forEach(add_render_callback);
}
function destroy_component(component, detaching) {
    const $$ = component.$$;
    if ($$.fragment !== null) {
        flush_render_callbacks($$.after_update);
        run_all($$.on_destroy);
        $$.fragment && $$.fragment.d(detaching);
        // TODO null out other refs, including component.$$ (but need to
        // preserve final state?)
        $$.on_destroy = $$.fragment = null;
        $$.ctx = [];
    }
}
function make_dirty(component, i) {
    if (component.$$.dirty[0] === -1) {
        dirty_components.push(component);
        schedule_update();
        component.$$.dirty.fill(0);
    }
    component.$$.dirty[(i / 31) | 0] |= (1 << (i % 31));
}
function init(component, options, instance, create_fragment, not_equal, props, append_styles, dirty = [-1]) {
    const parent_component = current_component;
    set_current_component(component);
    const $$ = component.$$ = {
        fragment: null,
        ctx: [],
        // state
        props,
        update: noop,
        not_equal,
        bound: blank_object(),
        // lifecycle
        on_mount: [],
        on_destroy: [],
        on_disconnect: [],
        before_update: [],
        after_update: [],
        context: new Map(options.context || (parent_component ? parent_component.$$.context : [])),
        // everything else
        callbacks: blank_object(),
        dirty,
        skip_bound: false,
        root: options.target || parent_component.$$.root
    };
    append_styles && append_styles($$.root);
    let ready = false;
    $$.ctx = instance
        ? instance(component, options.props || {}, (i, ret, ...rest) => {
            const value = rest.length ? rest[0] : ret;
            if ($$.ctx && not_equal($$.ctx[i], $$.ctx[i] = value)) {
                if (!$$.skip_bound && $$.bound[i])
                    $$.bound[i](value);
                if (ready)
                    make_dirty(component, i);
            }
            return ret;
        })
        : [];
    $$.update();
    ready = true;
    run_all($$.before_update);
    // `false` as a special case of no DOM component
    $$.fragment = create_fragment ? create_fragment($$.ctx) : false;
    if (options.target) {
        if (options.hydrate) {
            start_hydrating();
            const nodes = children(options.target);
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.l(nodes);
            nodes.forEach(detach);
        }
        else {
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.c();
        }
        if (options.intro)
            transition_in(component.$$.fragment);
        mount_component(component, options.target, options.anchor, options.customElement);
        end_hydrating();
        flush();
    }
    set_current_component(parent_component);
}
/**
 * Base class for Svelte components. Used when dev=false.
 */
class SvelteComponent {
    $destroy() {
        destroy_component(this, 1);
        this.$destroy = noop;
    }
    $on(type, callback) {
        if (!is_function(callback)) {
            return noop;
        }
        const callbacks = (this.$$.callbacks[type] || (this.$$.callbacks[type] = []));
        callbacks.push(callback);
        return () => {
            const index = callbacks.indexOf(callback);
            if (index !== -1)
                callbacks.splice(index, 1);
        };
    }
    $set($$props) {
        if (this.$$set && !is_empty($$props)) {
            this.$$.skip_bound = true;
            this.$$set($$props);
            this.$$.skip_bound = false;
        }
    }
}

/* generated by Svelte v3.58.0 */

function create_fragment(ctx) {
	let meta0;
	let meta1;
	let link0;
	let link1;
	let link2;
	let link3;
	let script0;
	let script0_src_value;
	let script1;
	let script1_src_value;
	let link4;
	let link4_href_value;
	let meta2;
	let meta3;
	let meta4;
	let meta5;
	let meta6;
	let style;
	let t;

	return {
		c() {
			meta0 = element("meta");
			meta1 = element("meta");
			link0 = element("link");
			link1 = element("link");
			link2 = element("link");
			link3 = element("link");
			script0 = element("script");
			script1 = element("script");
			link4 = element("link");
			meta2 = element("meta");
			meta3 = element("meta");
			meta4 = element("meta");
			meta5 = element("meta");
			meta6 = element("meta");
			style = element("style");
			t = text("@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\");\n\n:root {\n  /* Fonts  */\n  --font-heading: 'Fraunces', serif;\n  --font-body: 'IBM Plex Mono', monospace;\n  --font-text: 'Work Sans', sans-serif;\n  \n  /* Colors */\n  --color-Y500: #E9D90A;\n  --color-Y400: #F6E500;\n  --color-Y300: #F7D254;\n  --color-Y200: #FFF587;\n  --color-Y100: #FFFCDA;\n\n  --color-P500: #E82884;\n  --color-P400: #FF4FA3;\n  --color-P300: #FF74B7;\n  --color-P200: #FFB1D7;\n  --color-P100: #FFD6E9;\n\n  --color-T500: #50ADBE;\n  --color-T400: #69C9DB;\n  --color-T300: #A8E1EC;\n  --color-T200: #C2F1FA;\n  --color-T100: #E2FAFF;\n\n  --color-G500: #C8C9DC;\n  --color-G400: #D5D7EF;\n  --color-G300: #E6E7FB;\n  --color-G200: #EEF2FD;\n  --color-G100: #F4F9FC;\n\n  --color-black: #000000;\n  --color-white: #FFFFFF;\n  \n  /* Base values */\n  --color-primary: var(--color-Y400);\n  --color-secondary: var(--color-P400);\n  --color-tertiary: var(--color-black);\n  --color-tertiary: var(--color-white);\n  \n  /* --color: var(--color-base);\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 8px;\n  --border-color: #eee;\n  --background: white; */\n  --border: 0.851905px solid var(--color-black);\n  --border-radius: 4.25952px;\n  --max-content-width-mobile: 768px;\n  --max-content-width-small-desktop: 900px;\n  --max-content-width: 1200px;\n  --page-padding-desktop: 90px 80px;\n  --page-padding-small-desktop: 120px 60px;\n  --page-padding-mobile: 90px 18px;\n\n  --hero-padding-desktop: 150px 80px 90px 80px;\n  --hero-padding-large-desktop: 200px 80px 90px 80px;\n\n  --hero-padding-mobile: 100px 18px 90px 18px;\n  --content-padding: 0px 50px;\n  \n}\n\n\n#page a {\n    color: var(--color-black);\n  }\n\n\n#page h1,#page h2,#page h3,#page h4 {\n    font-family: var(--font-heading);\n    font-weight: 700;\n    color: var(--color-black);\n  }\n\n\n#page h1 {\n    font-size: 33px;\n    line-height: 39px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h1 {\n      font-size:  67px;\n      line-height: 69px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h1 {\n      font-size:  83px;\n      line-height: 93px\n  }\n    }\n\n\n#page h2 {\n    font-size: 28px;\n    line-height: 33px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h2 {\n      font-size:  55px;\n      line-height: 65px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h2 {\n      font-size:  65px;\n      line-height: 75px\n  }\n    }\n\n\n#page h3 {\n    font-size: 28px;\n    line-height: 33px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h3 {\n      font-size:  45px;\n      line-height: 57px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h3 {\n      font-size:  55px;\n      line-height: 68px\n  }\n    }\n\n\n#page h4 {\n    font-size: 26px;\n    line-height: 34px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h4 {\n      font-size:  37px;\n      line-height: 50px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h4 {\n      font-size:  45px;\n      line-height: 58px\n  }\n    }\n\n\n#page h5, #page h6, #page .h650, #page .h700, #page .h800, #page .h900, #page .h950 {\n    font-family: var(--font-body);\n    color: var(--color-black);\n  }\n\n\n#page h5 {\n    font-weight: 700;\n    font-size: 20px;\n    line-height: 28px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h5 {\n      font-size:  30px;\n      line-height: 39px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h5 {\n      font-size:  30px;\n      line-height: 39px\n  }\n    }\n\n\n#page h6 {\n    font-weight: 700;\n    font-size: 18px;\n    line-height: 26px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h6 {\n      font-size:  21px;\n      line-height: 29px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h6 {\n      font-size:  25px;\n      line-height: 33px\n  }\n    }\n\n\n#page .h650 {\n    font-weight: 500;\n    font-size: 18px;\n    line-height: 26px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h650 {\n      font-size:  21px;\n      line-height: 29px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h650 {\n      font-size:  25px;\n      line-height: 33px\n  }\n    }\n\n\n#page .h700 {\n    font-weight: 700;\n    font-size: 16px;\n    line-height: 20px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h700 {\n      font-size:  16px;\n      line-height: 20px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h700 {\n      font-size:  18px;\n      line-height: 25px\n  }\n    }\n\n\n#page .h800 {\n    font-weight: 500;\n    font-size: 12px;\n    line-height: 16px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h800 {\n      font-size:  12px;\n      line-height: 16px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h800 {\n      font-size:  17px;\n      line-height: 22px\n  }\n    }\n\n\n#page .h900 {\n    font-weight: 700;\n    font-size: 14px;\n    line-height: 20px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h900 {\n      font-size:  14px;\n      line-height: 20px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h900 {\n      font-size:  16px;\n      line-height: 22px\n  }\n    }\n\n\n#page .h950 {\n    font-weight: 500;\n    font-size: 14px;\n    line-height: 20px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h950 {\n      font-size:  14px;\n      line-height: 20px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h950 {\n      font-size:  16px;\n      line-height: 22px\n  }\n    }\n\n\n#page p {\n    font-family: var(--font-text);\n    font-weight: 400;\n    color: var(--color-black);\n  }\n\n\n#page .p-large {\n    font-size: 17px;\n    line-height: 26px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .p-large {\n      font-size:  18px;\n      line-height: 28px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .p-large {\n      font-size:  20px;\n      line-height: 31px\n  }\n    }\n\n\n#page .p-medium {\n    font-size: 15px;\n    line-height: 22px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .p-medium {\n      font-size:  15px;\n      line-height: 22px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .p-medium {\n      font-size:  17px;\n      line-height: 25px\n  }\n    }\n\n\n#page .p-small {\n    font-size: 13px;\n    line-height: 18px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .p-small {\n      font-size:  15px;\n      line-height: 22px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .p-small {\n      font-size:  14px;\n      line-height: 18px\n  }\n    }\n\n\n#page .link {\n    color: var(--color-P500);\n    -webkit-text-decoration-line: underline;\n            text-decoration-line: underline;\n  }\n\n\n#page .link:hover {\n      -webkit-text-decoration-line: unset;\n              text-decoration-line: unset;\n    }\n\n\n#page .link:active {\n      color: var(--color-P300);\n    }\n\n\n#page .link:visited {\n      color: var(--color-P500);\n      -webkit-text-decoration-line: underline;\n              text-decoration-line: underline;\n    }\n\n\n#page .tag-pink-large,\n  #page .tag-yellow-large,\n  #page .tag-lightyellow-large {\n    border-width: 2px;\n    border: var(--border);\n    border-radius: var(--border-radius);\n    padding: 0px 12.7786px;\n    gap: 8.52px;\n    height: 34.52px;\n    width: -webkit-max-content;\n    width: -moz-max-content;\n    width: max-content;\n    display: flex;\n    align-items: center;\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .tag-pink-large,\n  #page .tag-yellow-large,\n  #page .tag-lightyellow-large {\n      height: 41.52px\n  }\n    }\n\n\n#page .tag-pink-small,\n  #page .tag-yellow-small,\n  #page .tag-lightyellow-small {\n    border-width: 2px;\n    border: var(--border);\n    border-radius: var(--border-radius);\n    padding: 0px 10px;\n    gap: 8.52px;\n    height: 32px;\n    width: -webkit-max-content;\n    width: -moz-max-content;\n    width: max-content;\n    display: flex;\n    align-items: center;\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .tag-pink-small,\n  #page .tag-yellow-small,\n  #page .tag-lightyellow-small {\n      height: 37px\n  }\n    }\n\n\n#page .tag-pink-large {\n    background-color: var(--color-secondary);\n  }\n\n\n#page .tag-pink-small {\n    background-color: var(--color-secondary);\n  }\n\n\n#page .tag-yellow-large {\n    background-color: var(--color-primary);\n  }\n\n\n#page .tag-yellow-small {\n    background-color: var(--color-primary);\n  }\n\n\n#page .tag-lightyellow-large {\n    background-color: var(--color-Y100);\n  }\n\n\n#page .tag-lightyellow-small {\n    background-color: var(--color-Y100);\n  }\n\n\n#page .primary-large-button {\n    font-family: var(--font-body);\n    color: var(--color-black);\n    border-radius: 100px;\n    /* height: 60px; */\n    background-color: var(--color-black);\n    color: var(--color-white);\n    padding: 20px 35px;\n    font-weight: 700;\n    font-size: 16px;\n    line-height: 23px;\n    border: 2px solid var(--color-black);\n    transition: all 0.5s;\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .primary-large-button {\n      padding: 25px 40px;\n      font-weight: 700;\n      font-size: 18px;\n      line-height: 25px\n  }\n    }\n\n\n#page .primary-large-button:hover {\n      background: transparent;\n      color: var(--color-black);\n      border: 2px solid var(--color-black);\n    }\n\n\n#page .primary-large-button:active {\n      margin: -1px;\n      border: 3px solid var(--color-black);\n    }\n\n\n#page .primary-small-button {\n    font-family: var(--font-body);\n    color: var(--color-black);\n    border-radius: 100px;\n    /* height: 40px; */\n    background-color: var(--color-black);\n    color: var(--color-white);\n    padding: 10px 25px;\n    font-weight: 700;\n    font-size: 14px;\n    line-height: 20px;\n    transition: all 0.5s;\n    border: 2px solid var(--color-black);\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .primary-small-button {\n      padding: 15px 40px;\n      font-weight: 700;\n      font-size: 16px;\n      line-height: 22px\n  }\n    }\n\n\n#page .primary-small-button:hover {\n      background: transparent;\n      color: var(--color-black);\n      border: 2px solid var(--color-black);\n    }\n\n\n#page .primary-small-button:active {\n      margin: -1px;\n      border: 3px solid var(--color-black);\n    }\n\n\n#page .secondary-button {\n    font-family: var(--font-body); \n    color: var(--color-black);\n    border-radius: 100px;\n    height: 52px;\n    border: 3px solid var(--color-black);\n    color: var(--color-black);\n    transition: all 0.5s;\n    padding: 15px 34px;\n    font-weight: 700;\n    font-size: 14px;\n    line-height: 22px;\n    background: transparent;\n  }\n\n\n#page .secondary-button:hover {\n      background: var(--color-black);\n      color: var(--color-white);\n    }\n\n\n#page .secondary-button:active {\n      background: var(--color-G500);\n      border-color: var(--color-G500);\n    }");
			this.h();
		},
		l(nodes) {
			const head_nodes = head_selector('svelte-9afuw6', document.head);
			meta0 = claim_element(head_nodes, "META", { name: true, content: true });
			meta1 = claim_element(head_nodes, "META", { charset: true });
			link0 = claim_element(head_nodes, "LINK", { rel: true, href: true });
			link1 = claim_element(head_nodes, "LINK", { rel: true, href: true, crossorigin: true });
			link2 = claim_element(head_nodes, "LINK", { href: true, rel: true });
			link3 = claim_element(head_nodes, "LINK", { rel: true, type: true, href: true });
			script0 = claim_element(head_nodes, "SCRIPT", { type: true, src: true });
			var script0_nodes = children(script0);
			script0_nodes.forEach(detach);
			script1 = claim_element(head_nodes, "SCRIPT", { src: true });
			var script1_nodes = children(script1);
			script1_nodes.forEach(detach);

			link4 = claim_element(head_nodes, "LINK", {
				rel: true,
				type: true,
				sizes: true,
				href: true
			});

			meta2 = claim_element(head_nodes, "META", { charset: true });
			meta3 = claim_element(head_nodes, "META", { name: true, content: true });
			meta4 = claim_element(head_nodes, "META", { name: true, content: true });
			meta5 = claim_element(head_nodes, "META", { name: true, content: true });
			meta6 = claim_element(head_nodes, "META", { name: true, content: true });
			style = claim_element(head_nodes, "STYLE", {});
			var style_nodes = children(style);
			t = claim_text(style_nodes, "@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\");\n\n:root {\n  /* Fonts  */\n  --font-heading: 'Fraunces', serif;\n  --font-body: 'IBM Plex Mono', monospace;\n  --font-text: 'Work Sans', sans-serif;\n  \n  /* Colors */\n  --color-Y500: #E9D90A;\n  --color-Y400: #F6E500;\n  --color-Y300: #F7D254;\n  --color-Y200: #FFF587;\n  --color-Y100: #FFFCDA;\n\n  --color-P500: #E82884;\n  --color-P400: #FF4FA3;\n  --color-P300: #FF74B7;\n  --color-P200: #FFB1D7;\n  --color-P100: #FFD6E9;\n\n  --color-T500: #50ADBE;\n  --color-T400: #69C9DB;\n  --color-T300: #A8E1EC;\n  --color-T200: #C2F1FA;\n  --color-T100: #E2FAFF;\n\n  --color-G500: #C8C9DC;\n  --color-G400: #D5D7EF;\n  --color-G300: #E6E7FB;\n  --color-G200: #EEF2FD;\n  --color-G100: #F4F9FC;\n\n  --color-black: #000000;\n  --color-white: #FFFFFF;\n  \n  /* Base values */\n  --color-primary: var(--color-Y400);\n  --color-secondary: var(--color-P400);\n  --color-tertiary: var(--color-black);\n  --color-tertiary: var(--color-white);\n  \n  /* --color: var(--color-base);\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 8px;\n  --border-color: #eee;\n  --background: white; */\n  --border: 0.851905px solid var(--color-black);\n  --border-radius: 4.25952px;\n  --max-content-width-mobile: 768px;\n  --max-content-width-small-desktop: 900px;\n  --max-content-width: 1200px;\n  --page-padding-desktop: 90px 80px;\n  --page-padding-small-desktop: 120px 60px;\n  --page-padding-mobile: 90px 18px;\n\n  --hero-padding-desktop: 150px 80px 90px 80px;\n  --hero-padding-large-desktop: 200px 80px 90px 80px;\n\n  --hero-padding-mobile: 100px 18px 90px 18px;\n  --content-padding: 0px 50px;\n  \n}\n\n\n#page a {\n    color: var(--color-black);\n  }\n\n\n#page h1,#page h2,#page h3,#page h4 {\n    font-family: var(--font-heading);\n    font-weight: 700;\n    color: var(--color-black);\n  }\n\n\n#page h1 {\n    font-size: 33px;\n    line-height: 39px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h1 {\n      font-size:  67px;\n      line-height: 69px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h1 {\n      font-size:  83px;\n      line-height: 93px\n  }\n    }\n\n\n#page h2 {\n    font-size: 28px;\n    line-height: 33px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h2 {\n      font-size:  55px;\n      line-height: 65px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h2 {\n      font-size:  65px;\n      line-height: 75px\n  }\n    }\n\n\n#page h3 {\n    font-size: 28px;\n    line-height: 33px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h3 {\n      font-size:  45px;\n      line-height: 57px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h3 {\n      font-size:  55px;\n      line-height: 68px\n  }\n    }\n\n\n#page h4 {\n    font-size: 26px;\n    line-height: 34px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h4 {\n      font-size:  37px;\n      line-height: 50px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h4 {\n      font-size:  45px;\n      line-height: 58px\n  }\n    }\n\n\n#page h5, #page h6, #page .h650, #page .h700, #page .h800, #page .h900, #page .h950 {\n    font-family: var(--font-body);\n    color: var(--color-black);\n  }\n\n\n#page h5 {\n    font-weight: 700;\n    font-size: 20px;\n    line-height: 28px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h5 {\n      font-size:  30px;\n      line-height: 39px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h5 {\n      font-size:  30px;\n      line-height: 39px\n  }\n    }\n\n\n#page h6 {\n    font-weight: 700;\n    font-size: 18px;\n    line-height: 26px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h6 {\n      font-size:  21px;\n      line-height: 29px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h6 {\n      font-size:  25px;\n      line-height: 33px\n  }\n    }\n\n\n#page .h650 {\n    font-weight: 500;\n    font-size: 18px;\n    line-height: 26px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h650 {\n      font-size:  21px;\n      line-height: 29px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h650 {\n      font-size:  25px;\n      line-height: 33px\n  }\n    }\n\n\n#page .h700 {\n    font-weight: 700;\n    font-size: 16px;\n    line-height: 20px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h700 {\n      font-size:  16px;\n      line-height: 20px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h700 {\n      font-size:  18px;\n      line-height: 25px\n  }\n    }\n\n\n#page .h800 {\n    font-weight: 500;\n    font-size: 12px;\n    line-height: 16px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h800 {\n      font-size:  12px;\n      line-height: 16px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h800 {\n      font-size:  17px;\n      line-height: 22px\n  }\n    }\n\n\n#page .h900 {\n    font-weight: 700;\n    font-size: 14px;\n    line-height: 20px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h900 {\n      font-size:  14px;\n      line-height: 20px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h900 {\n      font-size:  16px;\n      line-height: 22px\n  }\n    }\n\n\n#page .h950 {\n    font-weight: 500;\n    font-size: 14px;\n    line-height: 20px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h950 {\n      font-size:  14px;\n      line-height: 20px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h950 {\n      font-size:  16px;\n      line-height: 22px\n  }\n    }\n\n\n#page p {\n    font-family: var(--font-text);\n    font-weight: 400;\n    color: var(--color-black);\n  }\n\n\n#page .p-large {\n    font-size: 17px;\n    line-height: 26px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .p-large {\n      font-size:  18px;\n      line-height: 28px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .p-large {\n      font-size:  20px;\n      line-height: 31px\n  }\n    }\n\n\n#page .p-medium {\n    font-size: 15px;\n    line-height: 22px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .p-medium {\n      font-size:  15px;\n      line-height: 22px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .p-medium {\n      font-size:  17px;\n      line-height: 25px\n  }\n    }\n\n\n#page .p-small {\n    font-size: 13px;\n    line-height: 18px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .p-small {\n      font-size:  15px;\n      line-height: 22px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .p-small {\n      font-size:  14px;\n      line-height: 18px\n  }\n    }\n\n\n#page .link {\n    color: var(--color-P500);\n    -webkit-text-decoration-line: underline;\n            text-decoration-line: underline;\n  }\n\n\n#page .link:hover {\n      -webkit-text-decoration-line: unset;\n              text-decoration-line: unset;\n    }\n\n\n#page .link:active {\n      color: var(--color-P300);\n    }\n\n\n#page .link:visited {\n      color: var(--color-P500);\n      -webkit-text-decoration-line: underline;\n              text-decoration-line: underline;\n    }\n\n\n#page .tag-pink-large,\n  #page .tag-yellow-large,\n  #page .tag-lightyellow-large {\n    border-width: 2px;\n    border: var(--border);\n    border-radius: var(--border-radius);\n    padding: 0px 12.7786px;\n    gap: 8.52px;\n    height: 34.52px;\n    width: -webkit-max-content;\n    width: -moz-max-content;\n    width: max-content;\n    display: flex;\n    align-items: center;\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .tag-pink-large,\n  #page .tag-yellow-large,\n  #page .tag-lightyellow-large {\n      height: 41.52px\n  }\n    }\n\n\n#page .tag-pink-small,\n  #page .tag-yellow-small,\n  #page .tag-lightyellow-small {\n    border-width: 2px;\n    border: var(--border);\n    border-radius: var(--border-radius);\n    padding: 0px 10px;\n    gap: 8.52px;\n    height: 32px;\n    width: -webkit-max-content;\n    width: -moz-max-content;\n    width: max-content;\n    display: flex;\n    align-items: center;\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .tag-pink-small,\n  #page .tag-yellow-small,\n  #page .tag-lightyellow-small {\n      height: 37px\n  }\n    }\n\n\n#page .tag-pink-large {\n    background-color: var(--color-secondary);\n  }\n\n\n#page .tag-pink-small {\n    background-color: var(--color-secondary);\n  }\n\n\n#page .tag-yellow-large {\n    background-color: var(--color-primary);\n  }\n\n\n#page .tag-yellow-small {\n    background-color: var(--color-primary);\n  }\n\n\n#page .tag-lightyellow-large {\n    background-color: var(--color-Y100);\n  }\n\n\n#page .tag-lightyellow-small {\n    background-color: var(--color-Y100);\n  }\n\n\n#page .primary-large-button {\n    font-family: var(--font-body);\n    color: var(--color-black);\n    border-radius: 100px;\n    /* height: 60px; */\n    background-color: var(--color-black);\n    color: var(--color-white);\n    padding: 20px 35px;\n    font-weight: 700;\n    font-size: 16px;\n    line-height: 23px;\n    border: 2px solid var(--color-black);\n    transition: all 0.5s;\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .primary-large-button {\n      padding: 25px 40px;\n      font-weight: 700;\n      font-size: 18px;\n      line-height: 25px\n  }\n    }\n\n\n#page .primary-large-button:hover {\n      background: transparent;\n      color: var(--color-black);\n      border: 2px solid var(--color-black);\n    }\n\n\n#page .primary-large-button:active {\n      margin: -1px;\n      border: 3px solid var(--color-black);\n    }\n\n\n#page .primary-small-button {\n    font-family: var(--font-body);\n    color: var(--color-black);\n    border-radius: 100px;\n    /* height: 40px; */\n    background-color: var(--color-black);\n    color: var(--color-white);\n    padding: 10px 25px;\n    font-weight: 700;\n    font-size: 14px;\n    line-height: 20px;\n    transition: all 0.5s;\n    border: 2px solid var(--color-black);\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .primary-small-button {\n      padding: 15px 40px;\n      font-weight: 700;\n      font-size: 16px;\n      line-height: 22px\n  }\n    }\n\n\n#page .primary-small-button:hover {\n      background: transparent;\n      color: var(--color-black);\n      border: 2px solid var(--color-black);\n    }\n\n\n#page .primary-small-button:active {\n      margin: -1px;\n      border: 3px solid var(--color-black);\n    }\n\n\n#page .secondary-button {\n    font-family: var(--font-body); \n    color: var(--color-black);\n    border-radius: 100px;\n    height: 52px;\n    border: 3px solid var(--color-black);\n    color: var(--color-black);\n    transition: all 0.5s;\n    padding: 15px 34px;\n    font-weight: 700;\n    font-size: 14px;\n    line-height: 22px;\n    background: transparent;\n  }\n\n\n#page .secondary-button:hover {\n      background: var(--color-black);\n      color: var(--color-white);\n    }\n\n\n#page .secondary-button:active {\n      background: var(--color-G500);\n      border-color: var(--color-G500);\n    }");
			style_nodes.forEach(detach);
			head_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(meta0, "name", "viewport");
			attr(meta0, "content", "width=device-width, initial-scale=1.0");
			attr(meta1, "charset", "UTF-8");
			attr(link0, "rel", "preconnect");
			attr(link0, "href", "https://fonts.googleapis.com");
			attr(link1, "rel", "preconnect");
			attr(link1, "href", "https://fonts.gstatic.com");
			attr(link1, "crossorigin", "");
			attr(link2, "href", "https://fonts.googleapis.com/css2?family=Fraunces:wght@700&family=IBM+Plex+Mono:wght@500;700&family=Work+Sans&display=swap");
			attr(link2, "rel", "stylesheet");
			attr(link3, "rel", "stylesheet");
			attr(link3, "type", "text/css");
			attr(link3, "href", "https://cdn.jsdelivr.net/npm/toastify-js/src/toastify.min.css");
			attr(script0, "type", "text/javascript");
			if (!src_url_equal(script0.src, script0_src_value = "https://cdn.jsdelivr.net/npm/toastify-js")) attr(script0, "src", script0_src_value);
			if (!src_url_equal(script1.src, script1_src_value = "https://unpkg.com/@lottiefiles/lottie-player@1.5.7/dist/lottie-player.js")) attr(script1, "src", script1_src_value);
			attr(link4, "rel", "icon");
			attr(link4, "type", "image/png");
			attr(link4, "sizes", "32x32");
			attr(link4, "href", link4_href_value = /*favicon*/ ctx[0].url);
			document.title = "UNLOK Loyalty | Tokenomics";
			attr(meta2, "charset", "UTF-8");
			attr(meta3, "name", "description");
			attr(meta3, "content", "Unleash the Power of Blockchain Rewards");
			attr(meta4, "name", "keywords");
			attr(meta4, "content", "Blockchain, Crypto, Cryptocurrency, Unlok, Rewards, Staking, Loyalty Program, Earn, Redeem");
			attr(meta5, "name", "author");
			attr(meta5, "content", "Unlok Loyalty");
			attr(meta6, "name", "viewport");
			attr(meta6, "content", "width=device-width, initial-scale=1.0");
		},
		m(target, anchor) {
			append_hydration(document.head, meta0);
			append_hydration(document.head, meta1);
			append_hydration(document.head, link0);
			append_hydration(document.head, link1);
			append_hydration(document.head, link2);
			append_hydration(document.head, link3);
			append_hydration(document.head, script0);
			append_hydration(document.head, script1);
			append_hydration(document.head, link4);
			append_hydration(document.head, meta2);
			append_hydration(document.head, meta3);
			append_hydration(document.head, meta4);
			append_hydration(document.head, meta5);
			append_hydration(document.head, meta6);
			append_hydration(document.head, style);
			append_hydration(style, t);
		},
		p(ctx, [dirty]) {
			if (dirty & /*favicon*/ 1 && link4_href_value !== (link4_href_value = /*favicon*/ ctx[0].url)) {
				attr(link4, "href", link4_href_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			detach(meta0);
			detach(meta1);
			detach(link0);
			detach(link1);
			detach(link2);
			detach(link3);
			detach(script0);
			detach(script1);
			detach(link4);
			detach(meta2);
			detach(meta3);
			detach(meta4);
			detach(meta5);
			detach(meta6);
			detach(style);
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { favicon } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(0, favicon = $$props.favicon);
	};

	return [favicon];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance, create_fragment, safe_not_equal, { favicon: 0 });
	}
}

function fade(node, { delay = 0, duration = 400, easing = identity } = {}) {
    const o = +getComputedStyle(node).opacity;
    return {
        delay,
        duration,
        easing,
        css: t => `opacity: ${t * o}`
    };
}

const matchIconName = /^[a-z0-9]+(-[a-z0-9]+)*$/;
const stringToIcon = (value, validate, allowSimpleName, provider = "") => {
  const colonSeparated = value.split(":");
  if (value.slice(0, 1) === "@") {
    if (colonSeparated.length < 2 || colonSeparated.length > 3) {
      return null;
    }
    provider = colonSeparated.shift().slice(1);
  }
  if (colonSeparated.length > 3 || !colonSeparated.length) {
    return null;
  }
  if (colonSeparated.length > 1) {
    const name2 = colonSeparated.pop();
    const prefix = colonSeparated.pop();
    const result = {
      provider: colonSeparated.length > 0 ? colonSeparated[0] : provider,
      prefix,
      name: name2
    };
    return validate && !validateIconName(result) ? null : result;
  }
  const name = colonSeparated[0];
  const dashSeparated = name.split("-");
  if (dashSeparated.length > 1) {
    const result = {
      provider,
      prefix: dashSeparated.shift(),
      name: dashSeparated.join("-")
    };
    return validate && !validateIconName(result) ? null : result;
  }
  if (allowSimpleName && provider === "") {
    const result = {
      provider,
      prefix: "",
      name
    };
    return validate && !validateIconName(result, allowSimpleName) ? null : result;
  }
  return null;
};
const validateIconName = (icon, allowSimpleName) => {
  if (!icon) {
    return false;
  }
  return !!((icon.provider === "" || icon.provider.match(matchIconName)) && (allowSimpleName && icon.prefix === "" || icon.prefix.match(matchIconName)) && icon.name.match(matchIconName));
};
const defaultIconDimensions = Object.freeze({
  left: 0,
  top: 0,
  width: 16,
  height: 16
});
const defaultIconTransformations = Object.freeze({
  rotate: 0,
  vFlip: false,
  hFlip: false
});
const defaultIconProps = Object.freeze({
  ...defaultIconDimensions,
  ...defaultIconTransformations
});
const defaultExtendedIconProps = Object.freeze({
  ...defaultIconProps,
  body: "",
  hidden: false
});
function mergeIconTransformations(obj1, obj2) {
  const result = {};
  if (!obj1.hFlip !== !obj2.hFlip) {
    result.hFlip = true;
  }
  if (!obj1.vFlip !== !obj2.vFlip) {
    result.vFlip = true;
  }
  const rotate = ((obj1.rotate || 0) + (obj2.rotate || 0)) % 4;
  if (rotate) {
    result.rotate = rotate;
  }
  return result;
}
function mergeIconData(parent, child) {
  const result = mergeIconTransformations(parent, child);
  for (const key in defaultExtendedIconProps) {
    if (key in defaultIconTransformations) {
      if (key in parent && !(key in result)) {
        result[key] = defaultIconTransformations[key];
      }
    } else if (key in child) {
      result[key] = child[key];
    } else if (key in parent) {
      result[key] = parent[key];
    }
  }
  return result;
}
function getIconsTree(data, names) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  const resolved = /* @__PURE__ */ Object.create(null);
  function resolve(name) {
    if (icons[name]) {
      return resolved[name] = [];
    }
    if (!(name in resolved)) {
      resolved[name] = null;
      const parent = aliases[name] && aliases[name].parent;
      const value = parent && resolve(parent);
      if (value) {
        resolved[name] = [parent].concat(value);
      }
    }
    return resolved[name];
  }
  (names || Object.keys(icons).concat(Object.keys(aliases))).forEach(resolve);
  return resolved;
}
function internalGetIconData(data, name, tree) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  let currentProps = {};
  function parse(name2) {
    currentProps = mergeIconData(icons[name2] || aliases[name2], currentProps);
  }
  parse(name);
  tree.forEach(parse);
  return mergeIconData(data, currentProps);
}
function parseIconSet(data, callback) {
  const names = [];
  if (typeof data !== "object" || typeof data.icons !== "object") {
    return names;
  }
  if (data.not_found instanceof Array) {
    data.not_found.forEach((name) => {
      callback(name, null);
      names.push(name);
    });
  }
  const tree = getIconsTree(data);
  for (const name in tree) {
    const item = tree[name];
    if (item) {
      callback(name, internalGetIconData(data, name, item));
      names.push(name);
    }
  }
  return names;
}
const optionalPropertyDefaults = {
  provider: "",
  aliases: {},
  not_found: {},
  ...defaultIconDimensions
};
function checkOptionalProps(item, defaults) {
  for (const prop in defaults) {
    if (prop in item && typeof item[prop] !== typeof defaults[prop]) {
      return false;
    }
  }
  return true;
}
function quicklyValidateIconSet(obj) {
  if (typeof obj !== "object" || obj === null) {
    return null;
  }
  const data = obj;
  if (typeof data.prefix !== "string" || !obj.icons || typeof obj.icons !== "object") {
    return null;
  }
  if (!checkOptionalProps(obj, optionalPropertyDefaults)) {
    return null;
  }
  const icons = data.icons;
  for (const name in icons) {
    const icon = icons[name];
    if (!name.match(matchIconName) || typeof icon.body !== "string" || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  for (const name in aliases) {
    const icon = aliases[name];
    const parent = icon.parent;
    if (!name.match(matchIconName) || typeof parent !== "string" || !icons[parent] && !aliases[parent] || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  return data;
}
const dataStorage = /* @__PURE__ */ Object.create(null);
function newStorage(provider, prefix) {
  return {
    provider,
    prefix,
    icons: /* @__PURE__ */ Object.create(null),
    missing: /* @__PURE__ */ new Set()
  };
}
function getStorage(provider, prefix) {
  const providerStorage = dataStorage[provider] || (dataStorage[provider] = /* @__PURE__ */ Object.create(null));
  return providerStorage[prefix] || (providerStorage[prefix] = newStorage(provider, prefix));
}
function addIconSet(storage2, data) {
  if (!quicklyValidateIconSet(data)) {
    return [];
  }
  return parseIconSet(data, (name, icon) => {
    if (icon) {
      storage2.icons[name] = icon;
    } else {
      storage2.missing.add(name);
    }
  });
}
function addIconToStorage(storage2, name, icon) {
  try {
    if (typeof icon.body === "string") {
      storage2.icons[name] = {...icon};
      return true;
    }
  } catch (err) {
  }
  return false;
}
let simpleNames = false;
function allowSimpleNames(allow) {
  if (typeof allow === "boolean") {
    simpleNames = allow;
  }
  return simpleNames;
}
function getIconData(name) {
  const icon = typeof name === "string" ? stringToIcon(name, true, simpleNames) : name;
  if (icon) {
    const storage2 = getStorage(icon.provider, icon.prefix);
    const iconName = icon.name;
    return storage2.icons[iconName] || (storage2.missing.has(iconName) ? null : void 0);
  }
}
function addIcon(name, data) {
  const icon = stringToIcon(name, true, simpleNames);
  if (!icon) {
    return false;
  }
  const storage2 = getStorage(icon.provider, icon.prefix);
  return addIconToStorage(storage2, icon.name, data);
}
function addCollection(data, provider) {
  if (typeof data !== "object") {
    return false;
  }
  if (typeof provider !== "string") {
    provider = data.provider || "";
  }
  if (simpleNames && !provider && !data.prefix) {
    let added = false;
    if (quicklyValidateIconSet(data)) {
      data.prefix = "";
      parseIconSet(data, (name, icon) => {
        if (icon && addIcon(name, icon)) {
          added = true;
        }
      });
    }
    return added;
  }
  const prefix = data.prefix;
  if (!validateIconName({
    provider,
    prefix,
    name: "a"
  })) {
    return false;
  }
  const storage2 = getStorage(provider, prefix);
  return !!addIconSet(storage2, data);
}
const defaultIconSizeCustomisations = Object.freeze({
  width: null,
  height: null
});
const defaultIconCustomisations = Object.freeze({
  ...defaultIconSizeCustomisations,
  ...defaultIconTransformations
});
const unitsSplit = /(-?[0-9.]*[0-9]+[0-9.]*)/g;
const unitsTest = /^-?[0-9.]*[0-9]+[0-9.]*$/g;
function calculateSize(size, ratio, precision) {
  if (ratio === 1) {
    return size;
  }
  precision = precision || 100;
  if (typeof size === "number") {
    return Math.ceil(size * ratio * precision) / precision;
  }
  if (typeof size !== "string") {
    return size;
  }
  const oldParts = size.split(unitsSplit);
  if (oldParts === null || !oldParts.length) {
    return size;
  }
  const newParts = [];
  let code = oldParts.shift();
  let isNumber = unitsTest.test(code);
  while (true) {
    if (isNumber) {
      const num = parseFloat(code);
      if (isNaN(num)) {
        newParts.push(code);
      } else {
        newParts.push(Math.ceil(num * ratio * precision) / precision);
      }
    } else {
      newParts.push(code);
    }
    code = oldParts.shift();
    if (code === void 0) {
      return newParts.join("");
    }
    isNumber = !isNumber;
  }
}
const isUnsetKeyword = (value) => value === "unset" || value === "undefined" || value === "none";
function iconToSVG(icon, customisations) {
  const fullIcon = {
    ...defaultIconProps,
    ...icon
  };
  const fullCustomisations = {
    ...defaultIconCustomisations,
    ...customisations
  };
  const box = {
    left: fullIcon.left,
    top: fullIcon.top,
    width: fullIcon.width,
    height: fullIcon.height
  };
  let body = fullIcon.body;
  [fullIcon, fullCustomisations].forEach((props) => {
    const transformations = [];
    const hFlip = props.hFlip;
    const vFlip = props.vFlip;
    let rotation = props.rotate;
    if (hFlip) {
      if (vFlip) {
        rotation += 2;
      } else {
        transformations.push("translate(" + (box.width + box.left).toString() + " " + (0 - box.top).toString() + ")");
        transformations.push("scale(-1 1)");
        box.top = box.left = 0;
      }
    } else if (vFlip) {
      transformations.push("translate(" + (0 - box.left).toString() + " " + (box.height + box.top).toString() + ")");
      transformations.push("scale(1 -1)");
      box.top = box.left = 0;
    }
    let tempValue;
    if (rotation < 0) {
      rotation -= Math.floor(rotation / 4) * 4;
    }
    rotation = rotation % 4;
    switch (rotation) {
      case 1:
        tempValue = box.height / 2 + box.top;
        transformations.unshift("rotate(90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
      case 2:
        transformations.unshift("rotate(180 " + (box.width / 2 + box.left).toString() + " " + (box.height / 2 + box.top).toString() + ")");
        break;
      case 3:
        tempValue = box.width / 2 + box.left;
        transformations.unshift("rotate(-90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
    }
    if (rotation % 2 === 1) {
      if (box.left !== box.top) {
        tempValue = box.left;
        box.left = box.top;
        box.top = tempValue;
      }
      if (box.width !== box.height) {
        tempValue = box.width;
        box.width = box.height;
        box.height = tempValue;
      }
    }
    if (transformations.length) {
      body = '<g transform="' + transformations.join(" ") + '">' + body + "</g>";
    }
  });
  const customisationsWidth = fullCustomisations.width;
  const customisationsHeight = fullCustomisations.height;
  const boxWidth = box.width;
  const boxHeight = box.height;
  let width;
  let height;
  if (customisationsWidth === null) {
    height = customisationsHeight === null ? "1em" : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
    width = calculateSize(height, boxWidth / boxHeight);
  } else {
    width = customisationsWidth === "auto" ? boxWidth : customisationsWidth;
    height = customisationsHeight === null ? calculateSize(width, boxHeight / boxWidth) : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
  }
  const attributes = {};
  const setAttr = (prop, value) => {
    if (!isUnsetKeyword(value)) {
      attributes[prop] = value.toString();
    }
  };
  setAttr("width", width);
  setAttr("height", height);
  attributes.viewBox = box.left.toString() + " " + box.top.toString() + " " + boxWidth.toString() + " " + boxHeight.toString();
  return {
    attributes,
    body
  };
}
const regex = /\sid="(\S+)"/g;
const randomPrefix = "IconifyId" + Date.now().toString(16) + (Math.random() * 16777216 | 0).toString(16);
let counter = 0;
function replaceIDs(body, prefix = randomPrefix) {
  const ids = [];
  let match;
  while (match = regex.exec(body)) {
    ids.push(match[1]);
  }
  if (!ids.length) {
    return body;
  }
  const suffix = "suffix" + (Math.random() * 16777216 | Date.now()).toString(16);
  ids.forEach((id) => {
    const newID = typeof prefix === "function" ? prefix(id) : prefix + (counter++).toString();
    const escapedID = id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    body = body.replace(new RegExp('([#;"])(' + escapedID + ')([")]|\\.[a-z])', "g"), "$1" + newID + suffix + "$3");
  });
  body = body.replace(new RegExp(suffix, "g"), "");
  return body;
}
const storage = /* @__PURE__ */ Object.create(null);
function setAPIModule(provider, item) {
  storage[provider] = item;
}
function getAPIModule(provider) {
  return storage[provider] || storage[""];
}
function createAPIConfig(source) {
  let resources;
  if (typeof source.resources === "string") {
    resources = [source.resources];
  } else {
    resources = source.resources;
    if (!(resources instanceof Array) || !resources.length) {
      return null;
    }
  }
  const result = {
    resources,
    path: source.path || "/",
    maxURL: source.maxURL || 500,
    rotate: source.rotate || 750,
    timeout: source.timeout || 5e3,
    random: source.random === true,
    index: source.index || 0,
    dataAfterTimeout: source.dataAfterTimeout !== false
  };
  return result;
}
const configStorage = /* @__PURE__ */ Object.create(null);
const fallBackAPISources = [
  "https://api.simplesvg.com",
  "https://api.unisvg.com"
];
const fallBackAPI = [];
while (fallBackAPISources.length > 0) {
  if (fallBackAPISources.length === 1) {
    fallBackAPI.push(fallBackAPISources.shift());
  } else {
    if (Math.random() > 0.5) {
      fallBackAPI.push(fallBackAPISources.shift());
    } else {
      fallBackAPI.push(fallBackAPISources.pop());
    }
  }
}
configStorage[""] = createAPIConfig({
  resources: ["https://api.iconify.design"].concat(fallBackAPI)
});
function addAPIProvider(provider, customConfig) {
  const config = createAPIConfig(customConfig);
  if (config === null) {
    return false;
  }
  configStorage[provider] = config;
  return true;
}
function getAPIConfig(provider) {
  return configStorage[provider];
}
const detectFetch = () => {
  let callback;
  try {
    callback = fetch;
    if (typeof callback === "function") {
      return callback;
    }
  } catch (err) {
  }
};
let fetchModule = detectFetch();
function calculateMaxLength(provider, prefix) {
  const config = getAPIConfig(provider);
  if (!config) {
    return 0;
  }
  let result;
  if (!config.maxURL) {
    result = 0;
  } else {
    let maxHostLength = 0;
    config.resources.forEach((item) => {
      const host = item;
      maxHostLength = Math.max(maxHostLength, host.length);
    });
    const url = prefix + ".json?icons=";
    result = config.maxURL - maxHostLength - config.path.length - url.length;
  }
  return result;
}
function shouldAbort(status) {
  return status === 404;
}
const prepare = (provider, prefix, icons) => {
  const results = [];
  const maxLength = calculateMaxLength(provider, prefix);
  const type = "icons";
  let item = {
    type,
    provider,
    prefix,
    icons: []
  };
  let length = 0;
  icons.forEach((name, index) => {
    length += name.length + 1;
    if (length >= maxLength && index > 0) {
      results.push(item);
      item = {
        type,
        provider,
        prefix,
        icons: []
      };
      length = name.length;
    }
    item.icons.push(name);
  });
  results.push(item);
  return results;
};
function getPath(provider) {
  if (typeof provider === "string") {
    const config = getAPIConfig(provider);
    if (config) {
      return config.path;
    }
  }
  return "/";
}
const send = (host, params, callback) => {
  if (!fetchModule) {
    callback("abort", 424);
    return;
  }
  let path = getPath(params.provider);
  switch (params.type) {
    case "icons": {
      const prefix = params.prefix;
      const icons = params.icons;
      const iconsList = icons.join(",");
      const urlParams = new URLSearchParams({
        icons: iconsList
      });
      path += prefix + ".json?" + urlParams.toString();
      break;
    }
    case "custom": {
      const uri = params.uri;
      path += uri.slice(0, 1) === "/" ? uri.slice(1) : uri;
      break;
    }
    default:
      callback("abort", 400);
      return;
  }
  let defaultError = 503;
  fetchModule(host + path).then((response) => {
    const status = response.status;
    if (status !== 200) {
      setTimeout(() => {
        callback(shouldAbort(status) ? "abort" : "next", status);
      });
      return;
    }
    defaultError = 501;
    return response.json();
  }).then((data) => {
    if (typeof data !== "object" || data === null) {
      setTimeout(() => {
        if (data === 404) {
          callback("abort", data);
        } else {
          callback("next", defaultError);
        }
      });
      return;
    }
    setTimeout(() => {
      callback("success", data);
    });
  }).catch(() => {
    callback("next", defaultError);
  });
};
const fetchAPIModule = {
  prepare,
  send
};
function sortIcons(icons) {
  const result = {
    loaded: [],
    missing: [],
    pending: []
  };
  const storage2 = /* @__PURE__ */ Object.create(null);
  icons.sort((a, b) => {
    if (a.provider !== b.provider) {
      return a.provider.localeCompare(b.provider);
    }
    if (a.prefix !== b.prefix) {
      return a.prefix.localeCompare(b.prefix);
    }
    return a.name.localeCompare(b.name);
  });
  let lastIcon = {
    provider: "",
    prefix: "",
    name: ""
  };
  icons.forEach((icon) => {
    if (lastIcon.name === icon.name && lastIcon.prefix === icon.prefix && lastIcon.provider === icon.provider) {
      return;
    }
    lastIcon = icon;
    const provider = icon.provider;
    const prefix = icon.prefix;
    const name = icon.name;
    const providerStorage = storage2[provider] || (storage2[provider] = /* @__PURE__ */ Object.create(null));
    const localStorage = providerStorage[prefix] || (providerStorage[prefix] = getStorage(provider, prefix));
    let list;
    if (name in localStorage.icons) {
      list = result.loaded;
    } else if (prefix === "" || localStorage.missing.has(name)) {
      list = result.missing;
    } else {
      list = result.pending;
    }
    const item = {
      provider,
      prefix,
      name
    };
    list.push(item);
  });
  return result;
}
function removeCallback(storages, id) {
  storages.forEach((storage2) => {
    const items = storage2.loaderCallbacks;
    if (items) {
      storage2.loaderCallbacks = items.filter((row) => row.id !== id);
    }
  });
}
function updateCallbacks(storage2) {
  if (!storage2.pendingCallbacksFlag) {
    storage2.pendingCallbacksFlag = true;
    setTimeout(() => {
      storage2.pendingCallbacksFlag = false;
      const items = storage2.loaderCallbacks ? storage2.loaderCallbacks.slice(0) : [];
      if (!items.length) {
        return;
      }
      let hasPending = false;
      const provider = storage2.provider;
      const prefix = storage2.prefix;
      items.forEach((item) => {
        const icons = item.icons;
        const oldLength = icons.pending.length;
        icons.pending = icons.pending.filter((icon) => {
          if (icon.prefix !== prefix) {
            return true;
          }
          const name = icon.name;
          if (storage2.icons[name]) {
            icons.loaded.push({
              provider,
              prefix,
              name
            });
          } else if (storage2.missing.has(name)) {
            icons.missing.push({
              provider,
              prefix,
              name
            });
          } else {
            hasPending = true;
            return true;
          }
          return false;
        });
        if (icons.pending.length !== oldLength) {
          if (!hasPending) {
            removeCallback([storage2], item.id);
          }
          item.callback(icons.loaded.slice(0), icons.missing.slice(0), icons.pending.slice(0), item.abort);
        }
      });
    });
  }
}
let idCounter = 0;
function storeCallback(callback, icons, pendingSources) {
  const id = idCounter++;
  const abort = removeCallback.bind(null, pendingSources, id);
  if (!icons.pending.length) {
    return abort;
  }
  const item = {
    id,
    icons,
    callback,
    abort
  };
  pendingSources.forEach((storage2) => {
    (storage2.loaderCallbacks || (storage2.loaderCallbacks = [])).push(item);
  });
  return abort;
}
function listToIcons(list, validate = true, simpleNames2 = false) {
  const result = [];
  list.forEach((item) => {
    const icon = typeof item === "string" ? stringToIcon(item, validate, simpleNames2) : item;
    if (icon) {
      result.push(icon);
    }
  });
  return result;
}
var defaultConfig = {
  resources: [],
  index: 0,
  timeout: 2e3,
  rotate: 750,
  random: false,
  dataAfterTimeout: false
};
function sendQuery(config, payload, query, done) {
  const resourcesCount = config.resources.length;
  const startIndex = config.random ? Math.floor(Math.random() * resourcesCount) : config.index;
  let resources;
  if (config.random) {
    let list = config.resources.slice(0);
    resources = [];
    while (list.length > 1) {
      const nextIndex = Math.floor(Math.random() * list.length);
      resources.push(list[nextIndex]);
      list = list.slice(0, nextIndex).concat(list.slice(nextIndex + 1));
    }
    resources = resources.concat(list);
  } else {
    resources = config.resources.slice(startIndex).concat(config.resources.slice(0, startIndex));
  }
  const startTime = Date.now();
  let status = "pending";
  let queriesSent = 0;
  let lastError;
  let timer = null;
  let queue = [];
  let doneCallbacks = [];
  if (typeof done === "function") {
    doneCallbacks.push(done);
  }
  function resetTimer() {
    if (timer) {
      clearTimeout(timer);
      timer = null;
    }
  }
  function abort() {
    if (status === "pending") {
      status = "aborted";
    }
    resetTimer();
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function subscribe(callback, overwrite) {
    if (overwrite) {
      doneCallbacks = [];
    }
    if (typeof callback === "function") {
      doneCallbacks.push(callback);
    }
  }
  function getQueryStatus() {
    return {
      startTime,
      payload,
      status,
      queriesSent,
      queriesPending: queue.length,
      subscribe,
      abort
    };
  }
  function failQuery() {
    status = "failed";
    doneCallbacks.forEach((callback) => {
      callback(void 0, lastError);
    });
  }
  function clearQueue() {
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function moduleResponse(item, response, data) {
    const isError = response !== "success";
    queue = queue.filter((queued) => queued !== item);
    switch (status) {
      case "pending":
        break;
      case "failed":
        if (isError || !config.dataAfterTimeout) {
          return;
        }
        break;
      default:
        return;
    }
    if (response === "abort") {
      lastError = data;
      failQuery();
      return;
    }
    if (isError) {
      lastError = data;
      if (!queue.length) {
        if (!resources.length) {
          failQuery();
        } else {
          execNext();
        }
      }
      return;
    }
    resetTimer();
    clearQueue();
    if (!config.random) {
      const index = config.resources.indexOf(item.resource);
      if (index !== -1 && index !== config.index) {
        config.index = index;
      }
    }
    status = "completed";
    doneCallbacks.forEach((callback) => {
      callback(data);
    });
  }
  function execNext() {
    if (status !== "pending") {
      return;
    }
    resetTimer();
    const resource = resources.shift();
    if (resource === void 0) {
      if (queue.length) {
        timer = setTimeout(() => {
          resetTimer();
          if (status === "pending") {
            clearQueue();
            failQuery();
          }
        }, config.timeout);
        return;
      }
      failQuery();
      return;
    }
    const item = {
      status: "pending",
      resource,
      callback: (status2, data) => {
        moduleResponse(item, status2, data);
      }
    };
    queue.push(item);
    queriesSent++;
    timer = setTimeout(execNext, config.rotate);
    query(resource, payload, item.callback);
  }
  setTimeout(execNext);
  return getQueryStatus;
}
function initRedundancy(cfg) {
  const config = {
    ...defaultConfig,
    ...cfg
  };
  let queries = [];
  function cleanup() {
    queries = queries.filter((item) => item().status === "pending");
  }
  function query(payload, queryCallback, doneCallback) {
    const query2 = sendQuery(config, payload, queryCallback, (data, error) => {
      cleanup();
      if (doneCallback) {
        doneCallback(data, error);
      }
    });
    queries.push(query2);
    return query2;
  }
  function find(callback) {
    return queries.find((value) => {
      return callback(value);
    }) || null;
  }
  const instance = {
    query,
    find,
    setIndex: (index) => {
      config.index = index;
    },
    getIndex: () => config.index,
    cleanup
  };
  return instance;
}
function emptyCallback$1() {
}
const redundancyCache = /* @__PURE__ */ Object.create(null);
function getRedundancyCache(provider) {
  if (!redundancyCache[provider]) {
    const config = getAPIConfig(provider);
    if (!config) {
      return;
    }
    const redundancy = initRedundancy(config);
    const cachedReundancy = {
      config,
      redundancy
    };
    redundancyCache[provider] = cachedReundancy;
  }
  return redundancyCache[provider];
}
function sendAPIQuery(target, query, callback) {
  let redundancy;
  let send2;
  if (typeof target === "string") {
    const api = getAPIModule(target);
    if (!api) {
      callback(void 0, 424);
      return emptyCallback$1;
    }
    send2 = api.send;
    const cached = getRedundancyCache(target);
    if (cached) {
      redundancy = cached.redundancy;
    }
  } else {
    const config = createAPIConfig(target);
    if (config) {
      redundancy = initRedundancy(config);
      const moduleKey = target.resources ? target.resources[0] : "";
      const api = getAPIModule(moduleKey);
      if (api) {
        send2 = api.send;
      }
    }
  }
  if (!redundancy || !send2) {
    callback(void 0, 424);
    return emptyCallback$1;
  }
  return redundancy.query(query, send2, callback)().abort;
}
const browserCacheVersion = "iconify2";
const browserCachePrefix = "iconify";
const browserCacheCountKey = browserCachePrefix + "-count";
const browserCacheVersionKey = browserCachePrefix + "-version";
const browserStorageHour = 36e5;
const browserStorageCacheExpiration = 168;
function getStoredItem(func, key) {
  try {
    return func.getItem(key);
  } catch (err) {
  }
}
function setStoredItem(func, key, value) {
  try {
    func.setItem(key, value);
    return true;
  } catch (err) {
  }
}
function removeStoredItem(func, key) {
  try {
    func.removeItem(key);
  } catch (err) {
  }
}
function setBrowserStorageItemsCount(storage2, value) {
  return setStoredItem(storage2, browserCacheCountKey, value.toString());
}
function getBrowserStorageItemsCount(storage2) {
  return parseInt(getStoredItem(storage2, browserCacheCountKey)) || 0;
}
const browserStorageConfig = {
  local: true,
  session: true
};
const browserStorageEmptyItems = {
  local: /* @__PURE__ */ new Set(),
  session: /* @__PURE__ */ new Set()
};
let browserStorageStatus = false;
function setBrowserStorageStatus(status) {
  browserStorageStatus = status;
}
let _window = typeof window === "undefined" ? {} : window;
function getBrowserStorage(key) {
  const attr = key + "Storage";
  try {
    if (_window && _window[attr] && typeof _window[attr].length === "number") {
      return _window[attr];
    }
  } catch (err) {
  }
  browserStorageConfig[key] = false;
}
function iterateBrowserStorage(key, callback) {
  const func = getBrowserStorage(key);
  if (!func) {
    return;
  }
  const version = getStoredItem(func, browserCacheVersionKey);
  if (version !== browserCacheVersion) {
    if (version) {
      const total2 = getBrowserStorageItemsCount(func);
      for (let i = 0; i < total2; i++) {
        removeStoredItem(func, browserCachePrefix + i.toString());
      }
    }
    setStoredItem(func, browserCacheVersionKey, browserCacheVersion);
    setBrowserStorageItemsCount(func, 0);
    return;
  }
  const minTime = Math.floor(Date.now() / browserStorageHour) - browserStorageCacheExpiration;
  const parseItem = (index) => {
    const name = browserCachePrefix + index.toString();
    const item = getStoredItem(func, name);
    if (typeof item !== "string") {
      return;
    }
    try {
      const data = JSON.parse(item);
      if (typeof data === "object" && typeof data.cached === "number" && data.cached > minTime && typeof data.provider === "string" && typeof data.data === "object" && typeof data.data.prefix === "string" && callback(data, index)) {
        return true;
      }
    } catch (err) {
    }
    removeStoredItem(func, name);
  };
  let total = getBrowserStorageItemsCount(func);
  for (let i = total - 1; i >= 0; i--) {
    if (!parseItem(i)) {
      if (i === total - 1) {
        total--;
        setBrowserStorageItemsCount(func, total);
      } else {
        browserStorageEmptyItems[key].add(i);
      }
    }
  }
}
function initBrowserStorage() {
  if (browserStorageStatus) {
    return;
  }
  setBrowserStorageStatus(true);
  for (const key in browserStorageConfig) {
    iterateBrowserStorage(key, (item) => {
      const iconSet = item.data;
      const provider = item.provider;
      const prefix = iconSet.prefix;
      const storage2 = getStorage(provider, prefix);
      if (!addIconSet(storage2, iconSet).length) {
        return false;
      }
      const lastModified = iconSet.lastModified || -1;
      storage2.lastModifiedCached = storage2.lastModifiedCached ? Math.min(storage2.lastModifiedCached, lastModified) : lastModified;
      return true;
    });
  }
}
function updateLastModified(storage2, lastModified) {
  const lastValue = storage2.lastModifiedCached;
  if (lastValue && lastValue >= lastModified) {
    return lastValue === lastModified;
  }
  storage2.lastModifiedCached = lastModified;
  if (lastValue) {
    for (const key in browserStorageConfig) {
      iterateBrowserStorage(key, (item) => {
        const iconSet = item.data;
        return item.provider !== storage2.provider || iconSet.prefix !== storage2.prefix || iconSet.lastModified === lastModified;
      });
    }
  }
  return true;
}
function storeInBrowserStorage(storage2, data) {
  if (!browserStorageStatus) {
    initBrowserStorage();
  }
  function store(key) {
    let func;
    if (!browserStorageConfig[key] || !(func = getBrowserStorage(key))) {
      return;
    }
    const set = browserStorageEmptyItems[key];
    let index;
    if (set.size) {
      set.delete(index = Array.from(set).shift());
    } else {
      index = getBrowserStorageItemsCount(func);
      if (!setBrowserStorageItemsCount(func, index + 1)) {
        return;
      }
    }
    const item = {
      cached: Math.floor(Date.now() / browserStorageHour),
      provider: storage2.provider,
      data
    };
    return setStoredItem(func, browserCachePrefix + index.toString(), JSON.stringify(item));
  }
  if (data.lastModified && !updateLastModified(storage2, data.lastModified)) {
    return;
  }
  if (!Object.keys(data.icons).length) {
    return;
  }
  if (data.not_found) {
    data = Object.assign({}, data);
    delete data.not_found;
  }
  if (!store("local")) {
    store("session");
  }
}
function emptyCallback() {
}
function loadedNewIcons(storage2) {
  if (!storage2.iconsLoaderFlag) {
    storage2.iconsLoaderFlag = true;
    setTimeout(() => {
      storage2.iconsLoaderFlag = false;
      updateCallbacks(storage2);
    });
  }
}
function loadNewIcons(storage2, icons) {
  if (!storage2.iconsToLoad) {
    storage2.iconsToLoad = icons;
  } else {
    storage2.iconsToLoad = storage2.iconsToLoad.concat(icons).sort();
  }
  if (!storage2.iconsQueueFlag) {
    storage2.iconsQueueFlag = true;
    setTimeout(() => {
      storage2.iconsQueueFlag = false;
      const {provider, prefix} = storage2;
      const icons2 = storage2.iconsToLoad;
      delete storage2.iconsToLoad;
      let api;
      if (!icons2 || !(api = getAPIModule(provider))) {
        return;
      }
      const params = api.prepare(provider, prefix, icons2);
      params.forEach((item) => {
        sendAPIQuery(provider, item, (data) => {
          if (typeof data !== "object") {
            item.icons.forEach((name) => {
              storage2.missing.add(name);
            });
          } else {
            try {
              const parsed = addIconSet(storage2, data);
              if (!parsed.length) {
                return;
              }
              const pending = storage2.pendingIcons;
              if (pending) {
                parsed.forEach((name) => {
                  pending.delete(name);
                });
              }
              storeInBrowserStorage(storage2, data);
            } catch (err) {
              console.error(err);
            }
          }
          loadedNewIcons(storage2);
        });
      });
    });
  }
}
const loadIcons = (icons, callback) => {
  const cleanedIcons = listToIcons(icons, true, allowSimpleNames());
  const sortedIcons = sortIcons(cleanedIcons);
  if (!sortedIcons.pending.length) {
    let callCallback = true;
    if (callback) {
      setTimeout(() => {
        if (callCallback) {
          callback(sortedIcons.loaded, sortedIcons.missing, sortedIcons.pending, emptyCallback);
        }
      });
    }
    return () => {
      callCallback = false;
    };
  }
  const newIcons = /* @__PURE__ */ Object.create(null);
  const sources = [];
  let lastProvider, lastPrefix;
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix} = icon;
    if (prefix === lastPrefix && provider === lastProvider) {
      return;
    }
    lastProvider = provider;
    lastPrefix = prefix;
    sources.push(getStorage(provider, prefix));
    const providerNewIcons = newIcons[provider] || (newIcons[provider] = /* @__PURE__ */ Object.create(null));
    if (!providerNewIcons[prefix]) {
      providerNewIcons[prefix] = [];
    }
  });
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix, name} = icon;
    const storage2 = getStorage(provider, prefix);
    const pendingQueue = storage2.pendingIcons || (storage2.pendingIcons = /* @__PURE__ */ new Set());
    if (!pendingQueue.has(name)) {
      pendingQueue.add(name);
      newIcons[provider][prefix].push(name);
    }
  });
  sources.forEach((storage2) => {
    const {provider, prefix} = storage2;
    if (newIcons[provider][prefix].length) {
      loadNewIcons(storage2, newIcons[provider][prefix]);
    }
  });
  return callback ? storeCallback(callback, sortedIcons, sources) : emptyCallback;
};
function mergeCustomisations(defaults, item) {
  const result = {
    ...defaults
  };
  for (const key in item) {
    const value = item[key];
    const valueType = typeof value;
    if (key in defaultIconSizeCustomisations) {
      if (value === null || value && (valueType === "string" || valueType === "number")) {
        result[key] = value;
      }
    } else if (valueType === typeof result[key]) {
      result[key] = key === "rotate" ? value % 4 : value;
    }
  }
  return result;
}
const separator = /[\s,]+/;
function flipFromString(custom, flip) {
  flip.split(separator).forEach((str) => {
    const value = str.trim();
    switch (value) {
      case "horizontal":
        custom.hFlip = true;
        break;
      case "vertical":
        custom.vFlip = true;
        break;
    }
  });
}
function rotateFromString(value, defaultValue = 0) {
  const units = value.replace(/^-?[0-9.]*/, "");
  function cleanup(value2) {
    while (value2 < 0) {
      value2 += 4;
    }
    return value2 % 4;
  }
  if (units === "") {
    const num = parseInt(value);
    return isNaN(num) ? 0 : cleanup(num);
  } else if (units !== value) {
    let split = 0;
    switch (units) {
      case "%":
        split = 25;
        break;
      case "deg":
        split = 90;
    }
    if (split) {
      let num = parseFloat(value.slice(0, value.length - units.length));
      if (isNaN(num)) {
        return 0;
      }
      num = num / split;
      return num % 1 === 0 ? cleanup(num) : 0;
    }
  }
  return defaultValue;
}
function iconToHTML(body, attributes) {
  let renderAttribsHTML = body.indexOf("xlink:") === -1 ? "" : ' xmlns:xlink="http://www.w3.org/1999/xlink"';
  for (const attr in attributes) {
    renderAttribsHTML += " " + attr + '="' + attributes[attr] + '"';
  }
  return '<svg xmlns="http://www.w3.org/2000/svg"' + renderAttribsHTML + ">" + body + "</svg>";
}
function encodeSVGforURL(svg) {
  return svg.replace(/"/g, "'").replace(/%/g, "%25").replace(/#/g, "%23").replace(/</g, "%3C").replace(/>/g, "%3E").replace(/\s+/g, " ");
}
function svgToData(svg) {
  return "data:image/svg+xml," + encodeSVGforURL(svg);
}
function svgToURL(svg) {
  return 'url("' + svgToData(svg) + '")';
}
const defaultExtendedIconCustomisations = {
  ...defaultIconCustomisations,
  inline: false
};
const svgDefaults = {
  xmlns: "http://www.w3.org/2000/svg",
  "xmlns:xlink": "http://www.w3.org/1999/xlink",
  "aria-hidden": true,
  role: "img"
};
const commonProps = {
  display: "inline-block"
};
const monotoneProps = {
  "background-color": "currentColor"
};
const coloredProps = {
  "background-color": "transparent"
};
const propsToAdd = {
  image: "var(--svg)",
  repeat: "no-repeat",
  size: "100% 100%"
};
const propsToAddTo = {
  "-webkit-mask": monotoneProps,
  mask: monotoneProps,
  background: coloredProps
};
for (const prefix in propsToAddTo) {
  const list = propsToAddTo[prefix];
  for (const prop in propsToAdd) {
    list[prefix + "-" + prop] = propsToAdd[prop];
  }
}
function fixSize(value) {
  return value + (value.match(/^[-0-9.]+$/) ? "px" : "");
}
function render(icon, props) {
  const customisations = mergeCustomisations(defaultExtendedIconCustomisations, props);
  const mode = props.mode || "svg";
  const componentProps = mode === "svg" ? {...svgDefaults} : {};
  if (icon.body.indexOf("xlink:") === -1) {
    delete componentProps["xmlns:xlink"];
  }
  let style = typeof props.style === "string" ? props.style : "";
  for (let key in props) {
    const value = props[key];
    if (value === void 0) {
      continue;
    }
    switch (key) {
      case "icon":
      case "style":
      case "onLoad":
      case "mode":
        break;
      case "inline":
      case "hFlip":
      case "vFlip":
        customisations[key] = value === true || value === "true" || value === 1;
        break;
      case "flip":
        if (typeof value === "string") {
          flipFromString(customisations, value);
        }
        break;
      case "color":
        style = style + (style.length > 0 && style.trim().slice(-1) !== ";" ? ";" : "") + "color: " + value + "; ";
        break;
      case "rotate":
        if (typeof value === "string") {
          customisations[key] = rotateFromString(value);
        } else if (typeof value === "number") {
          customisations[key] = value;
        }
        break;
      case "ariaHidden":
      case "aria-hidden":
        if (value !== true && value !== "true") {
          delete componentProps["aria-hidden"];
        }
        break;
      default:
        if (key.slice(0, 3) === "on:") {
          break;
        }
        if (defaultExtendedIconCustomisations[key] === void 0) {
          componentProps[key] = value;
        }
    }
  }
  const item = iconToSVG(icon, customisations);
  const renderAttribs = item.attributes;
  if (customisations.inline) {
    style = "vertical-align: -0.125em; " + style;
  }
  if (mode === "svg") {
    Object.assign(componentProps, renderAttribs);
    if (style !== "") {
      componentProps.style = style;
    }
    let localCounter = 0;
    let id = props.id;
    if (typeof id === "string") {
      id = id.replace(/-/g, "_");
    }
    return {
      svg: true,
      attributes: componentProps,
      body: replaceIDs(item.body, id ? () => id + "ID" + localCounter++ : "iconifySvelte")
    };
  }
  const {body, width, height} = icon;
  const useMask = mode === "mask" || (mode === "bg" ? false : body.indexOf("currentColor") !== -1);
  const html = iconToHTML(body, {
    ...renderAttribs,
    width: width + "",
    height: height + ""
  });
  const url = svgToURL(html);
  const styles = {
    "--svg": url
  };
  const size = (prop) => {
    const value = renderAttribs[prop];
    if (value) {
      styles[prop] = fixSize(value);
    }
  };
  size("width");
  size("height");
  Object.assign(styles, commonProps, useMask ? monotoneProps : coloredProps);
  let customStyle = "";
  for (const key in styles) {
    customStyle += key + ": " + styles[key] + ";";
  }
  componentProps.style = customStyle + style;
  return {
    svg: false,
    attributes: componentProps
  };
}
allowSimpleNames(true);
setAPIModule("", fetchAPIModule);
if (typeof document !== "undefined" && typeof window !== "undefined") {
  initBrowserStorage();
  const _window2 = window;
  if (_window2.IconifyPreload !== void 0) {
    const preload = _window2.IconifyPreload;
    const err = "Invalid IconifyPreload syntax.";
    if (typeof preload === "object" && preload !== null) {
      (preload instanceof Array ? preload : [preload]).forEach((item) => {
        try {
          if (typeof item !== "object" || item === null || item instanceof Array || typeof item.icons !== "object" || typeof item.prefix !== "string" || !addCollection(item)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      });
    }
  }
  if (_window2.IconifyProviders !== void 0) {
    const providers = _window2.IconifyProviders;
    if (typeof providers === "object" && providers !== null) {
      for (let key in providers) {
        const err = "IconifyProviders[" + key + "] is invalid.";
        try {
          const value = providers[key];
          if (typeof value !== "object" || !value || value.resources === void 0) {
            continue;
          }
          if (!addAPIProvider(key, value)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      }
    }
  }
}
function checkIconState(icon, state, mounted, callback, onload) {
  function abortLoading() {
    if (state.loading) {
      state.loading.abort();
      state.loading = null;
    }
  }
  if (typeof icon === "object" && icon !== null && typeof icon.body === "string") {
    state.name = "";
    abortLoading();
    return {data: {...defaultIconProps, ...icon}};
  }
  let iconName;
  if (typeof icon !== "string" || (iconName = stringToIcon(icon, false, true)) === null) {
    abortLoading();
    return null;
  }
  const data = getIconData(iconName);
  if (!data) {
    if (mounted && (!state.loading || state.loading.name !== icon)) {
      abortLoading();
      state.name = "";
      state.loading = {
        name: icon,
        abort: loadIcons([iconName], callback)
      };
    }
    return null;
  }
  abortLoading();
  if (state.name !== icon) {
    state.name = icon;
    if (onload && !state.destroyed) {
      onload(icon);
    }
  }
  const classes = ["iconify"];
  if (iconName.prefix !== "") {
    classes.push("iconify--" + iconName.prefix);
  }
  if (iconName.provider !== "") {
    classes.push("iconify--" + iconName.provider);
  }
  return {data, classes};
}
function generateIcon(icon, props) {
  return icon ? render({
    ...defaultIconProps,
    ...icon
  }, props) : null;
}
var checkIconState_1 = checkIconState;
var generateIcon_1 = generateIcon;

/* generated by Svelte v3.58.0 */

function create_if_block(ctx) {
	let if_block_anchor;

	function select_block_type(ctx, dirty) {
		if (/*data*/ ctx[0].svg) return create_if_block_1;
		return create_else_block;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type(ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, dirty) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			}
		},
		d(detaching) {
			if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

// (113:1) {:else}
function create_else_block(ctx) {
	let span;
	let span_levels = [/*data*/ ctx[0].attributes];
	let span_data = {};

	for (let i = 0; i < span_levels.length; i += 1) {
		span_data = assign(span_data, span_levels[i]);
	}

	return {
		c() {
			span = element("span");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", {});
			children(span).forEach(detach);
			this.h();
		},
		h() {
			set_attributes(span, span_data);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
		},
		p(ctx, dirty) {
			set_attributes(span, span_data = get_spread_update(span_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (109:1) {#if data.svg}
function create_if_block_1(ctx) {
	let svg;
	let raw_value = /*data*/ ctx[0].body + "";
	let svg_levels = [/*data*/ ctx[0].attributes];
	let svg_data = {};

	for (let i = 0; i < svg_levels.length; i += 1) {
		svg_data = assign(svg_data, svg_levels[i]);
	}

	return {
		c() {
			svg = svg_element("svg");
			this.h();
		},
		l(nodes) {
			svg = claim_svg_element(nodes, "svg", {});
			var svg_nodes = children(svg);
			svg_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_svg_attributes(svg, svg_data);
		},
		m(target, anchor) {
			insert_hydration(target, svg, anchor);
			svg.innerHTML = raw_value;
		},
		p(ctx, dirty) {
			if (dirty & /*data*/ 1 && raw_value !== (raw_value = /*data*/ ctx[0].body + "")) svg.innerHTML = raw_value;			set_svg_attributes(svg, svg_data = get_spread_update(svg_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(svg);
		}
	};
}

function create_fragment$1(ctx) {
	let if_block_anchor;
	let if_block = /*data*/ ctx[0] && create_if_block(ctx);

	return {
		c() {
			if (if_block) if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if (if_block) if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if (if_block) if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, [dirty]) {
			if (/*data*/ ctx[0]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block(ctx);
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (if_block) if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	const state = {
		// Last icon name
		name: '',
		// Loading status
		loading: null,
		// Destroyed status
		destroyed: false
	};

	// Mounted status
	let mounted = false;

	// Callback counter
	let counter = 0;

	// Generated data
	let data;

	const onLoad = icon => {
		// Legacy onLoad property
		if (typeof $$props.onLoad === 'function') {
			$$props.onLoad(icon);
		}

		// on:load event
		const dispatch = createEventDispatcher();

		dispatch('load', { icon });
	};

	// Increase counter when loaded to force re-calculation of data
	function loaded() {
		$$invalidate(3, counter++, counter);
	}

	// Force re-render
	onMount(() => {
		$$invalidate(2, mounted = true);
	});

	// Abort loading when component is destroyed
	onDestroy(() => {
		$$invalidate(1, state.destroyed = true, state);

		if (state.loading) {
			state.loading.abort();
			$$invalidate(1, state.loading = null, state);
		}
	});

	$$self.$$set = $$new_props => {
		$$invalidate(6, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
	};

	$$self.$$.update = () => {
		 {
			const iconData = checkIconState_1($$props.icon, state, mounted, loaded, onLoad);
			$$invalidate(0, data = iconData ? generateIcon_1(iconData.data, $$props) : null);

			if (data && iconData.classes) {
				// Add classes
				$$invalidate(
					0,
					data.attributes['class'] = (typeof $$props['class'] === 'string'
					? $$props['class'] + ' '
					: '') + iconData.classes.join(' '),
					data
				);
			}
		}
	};

	$$props = exclude_internal_props($$props);
	return [data, state, mounted, counter];
}

class Component$1 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$1, create_fragment$1, safe_not_equal, {});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[8] = list[i].link;
	return child_ctx;
}

function get_each_context_1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[8] = list[i].link;
	return child_ctx;
}

// (254:35) 
function create_if_block_4(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true, class: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
			attr(img, "class", "svelte-jc1u8d");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (252:10) {#if logo.title}
function create_if_block_3(ctx) {
	let t_value = /*logo*/ ctx[0].title + "";
	let t;

	return {
		c() {
			t = text(t_value);
		},
		l(nodes) {
			t = claim_text(nodes, t_value);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && t_value !== (t_value = /*logo*/ ctx[0].title + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (259:10) {#each site_nav as { link }}
function create_each_block_1(ctx) {
	let h6;
	let a;
	let t_value = /*link*/ ctx[8].label + "";
	let t;
	let a_class_value;
	let a_href_value;

	return {
		c() {
			h6 = element("h6");
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			h6 = claim_element(nodes, "H6", { class: true });
			var h6_nodes = children(h6);
			a = claim_element(h6_nodes, "A", { id: true, class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			h6_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "id", "nav-item");

			attr(a, "class", a_class_value = "" + (null_to_empty(window.location.pathname.includes(/*link*/ ctx[8].url)
			? 'active-link'
			: 'inactive-link') + " svelte-jc1u8d"));

			attr(a, "href", a_href_value = /*link*/ ctx[8].url);
			attr(h6, "class", "h950");
		},
		m(target, anchor) {
			insert_hydration(target, h6, anchor);
			append_hydration(h6, a);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[8].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_class_value !== (a_class_value = "" + (null_to_empty(window.location.pathname.includes(/*link*/ ctx[8].url)
			? 'active-link'
			: 'inactive-link') + " svelte-jc1u8d"))) {
				attr(a, "class", a_class_value);
			}

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[8].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(h6);
		}
	};
}

// (273:35) 
function create_if_block_2(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true, class: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
			attr(img, "class", "svelte-jc1u8d");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (271:10) {#if logo.title}
function create_if_block_1$1(ctx) {
	let t_value = /*logo*/ ctx[0].title + "";
	let t;

	return {
		c() {
			t = text(t_value);
		},
		l(nodes) {
			t = claim_text(nodes, t_value);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && t_value !== (t_value = /*logo*/ ctx[0].title + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (289:8) {#if mobileNavOpen}
function create_if_block$1(ctx) {
	let nav;
	let t0;
	let a;
	let t1_value = /*site_nav_button*/ ctx[2].label + "";
	let t1;
	let a_href_value;
	let t2;
	let button;
	let icon;
	let nav_transition;
	let current;
	let mounted;
	let dispose;
	let each_value = /*site_nav*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	icon = new Component$1({ props: { height: "25", icon: "bi:x-lg" } });

	return {
		c() {
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t0 = space();
			a = element("a");
			t1 = text(t1_value);
			t2 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			this.h();
		},
		l(nodes) {
			nav = claim_element(nodes, "NAV", { id: true, class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			t0 = claim_space(nav_nodes);
			a = claim_element(nav_nodes, "A", { class: true, id: true, href: true });
			var a_nodes = children(a);
			t1 = claim_text(a_nodes, t1_value);
			a_nodes.forEach(detach);
			t2 = claim_space(nav_nodes);

			button = claim_element(nav_nodes, "BUTTON", {
				id: true,
				"aria-label": true,
				class: true
			});

			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			nav_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "primary-small-button");
			attr(a, "id", "nav");
			attr(a, "href", a_href_value = /*site_nav_button*/ ctx[2].url);
			attr(button, "id", "close");
			attr(button, "aria-label", "Close Navigation");
			attr(button, "class", "svelte-jc1u8d");
			attr(nav, "id", "popup");
			attr(nav, "class", "svelte-jc1u8d");
		},
		m(target, anchor) {
			insert_hydration(target, nav, anchor);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(nav, t0);
			append_hydration(nav, a);
			append_hydration(a, t1);
			append_hydration(nav, t2);
			append_hydration(nav, button);
			mount_component(icon, button, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler_1*/ ctx[7]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (dirty & /*window, site_nav*/ 2) {
				each_value = /*site_nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, t0);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}

			if ((!current || dirty & /*site_nav_button*/ 4) && t1_value !== (t1_value = /*site_nav_button*/ ctx[2].label + "")) set_data(t1, t1_value);

			if (!current || dirty & /*site_nav_button*/ 4 && a_href_value !== (a_href_value = /*site_nav_button*/ ctx[2].url)) {
				attr(a, "href", a_href_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);

			add_render_callback(() => {
				if (!current) return;
				if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, true);
				nav_transition.run(1);
			});

			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, false);
			nav_transition.run(0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(nav);
			destroy_each(each_blocks, detaching);
			destroy_component(icon);
			if (detaching && nav_transition) nav_transition.end();
			mounted = false;
			dispose();
		}
	};
}

// (292:14) {#each site_nav as { link }}
function create_each_block(ctx) {
	let h6;
	let a;
	let t_value = /*link*/ ctx[8].label + "";
	let t;
	let a_class_value;
	let a_href_value;

	return {
		c() {
			h6 = element("h6");
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			h6 = claim_element(nodes, "H6", { class: true });
			var h6_nodes = children(h6);

			a = claim_element(h6_nodes, "A", {
				id: true,
				class: true,
				active: true,
				href: true
			});

			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			h6_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "id", "nav-item");

			attr(a, "class", a_class_value = "" + (null_to_empty(window.location.pathname.includes(/*link*/ ctx[8].url)
			? 'active-link'
			: 'inactive-link') + " svelte-jc1u8d"));

			attr(a, "active", "true");
			attr(a, "href", a_href_value = /*link*/ ctx[8].url);
			attr(h6, "class", "h950");
		},
		m(target, anchor) {
			insert_hydration(target, h6, anchor);
			append_hydration(h6, a);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[8].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_class_value !== (a_class_value = "" + (null_to_empty(window.location.pathname.includes(/*link*/ ctx[8].url)
			? 'active-link'
			: 'inactive-link') + " svelte-jc1u8d"))) {
				attr(a, "class", a_class_value);
			}

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[8].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(h6);
		}
	};
}

function create_fragment$2(ctx) {
	let div4;
	let header;
	let div3;
	let div2;
	let div0;
	let a0;
	let t0;
	let nav;
	let t1;
	let a1;
	let t2_value = /*site_nav_button*/ ctx[2].label + "";
	let t2;
	let a1_href_value;
	let t3;
	let div1;
	let a2;
	let t4;
	let button;
	let icon;
	let t5;
	let current;
	let mounted;
	let dispose;

	function select_block_type(ctx, dirty) {
		if (/*logo*/ ctx[0].title) return create_if_block_3;
		if (/*logo*/ ctx[0].image.url) return create_if_block_4;
	}

	let current_block_type = select_block_type(ctx);
	let if_block0 = current_block_type && current_block_type(ctx);
	let each_value_1 = /*site_nav*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1(get_each_context_1(ctx, each_value_1, i));
	}

	function select_block_type_1(ctx, dirty) {
		if (/*logo*/ ctx[0].title) return create_if_block_1$1;
		if (/*logo*/ ctx[0].image.url) return create_if_block_2;
	}

	let current_block_type_1 = select_block_type_1(ctx);
	let if_block1 = current_block_type_1 && current_block_type_1(ctx);

	icon = new Component$1({
			props: {
				height: "37",
				icon: "eva:menu-outline",
				style: "color:black;"
			}
		});

	let if_block2 = /*mobileNavOpen*/ ctx[3] && create_if_block$1(ctx);

	return {
		c() {
			div4 = element("div");
			header = element("header");
			div3 = element("div");
			div2 = element("div");
			div0 = element("div");
			a0 = element("a");
			if (if_block0) if_block0.c();
			t0 = space();
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t1 = space();
			a1 = element("a");
			t2 = text(t2_value);
			t3 = space();
			div1 = element("div");
			a2 = element("a");
			if (if_block1) if_block1.c();
			t4 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			t5 = space();
			if (if_block2) if_block2.c();
			this.h();
		},
		l(nodes) {
			div4 = claim_element(nodes, "DIV", { class: true, id: true });
			var div4_nodes = children(div4);
			header = claim_element(div4_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			div3 = claim_element(header_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			a0 = claim_element(div0_nodes, "A", { href: true, class: true });
			var a0_nodes = children(a0);
			if (if_block0) if_block0.l(a0_nodes);
			a0_nodes.forEach(detach);
			t0 = claim_space(div0_nodes);
			nav = claim_element(div0_nodes, "NAV", { style: true, class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			t1 = claim_space(nav_nodes);
			a1 = claim_element(nav_nodes, "A", { class: true, id: true, href: true });
			var a1_nodes = children(a1);
			t2 = claim_text(a1_nodes, t2_value);
			a1_nodes.forEach(detach);
			nav_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t3 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			a2 = claim_element(div1_nodes, "A", { href: true, class: true });
			var a2_nodes = children(a2);
			if (if_block1) if_block1.l(a2_nodes);
			a2_nodes.forEach(detach);
			t4 = claim_space(div1_nodes);
			button = claim_element(div1_nodes, "BUTTON", { id: true, "aria-label": true });
			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			t5 = claim_space(div1_nodes);
			if (if_block2) if_block2.l(div1_nodes);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			header_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a0, "href", "/");
			attr(a0, "class", "logo svelte-jc1u8d");
			attr(a1, "class", "primary-small-button");
			attr(a1, "id", "nav");
			attr(a1, "href", a1_href_value = /*site_nav_button*/ ctx[2].url);
			set_style(nav, "display", "flex");
			set_style(nav, "align-items", "center");
			attr(nav, "class", "svelte-jc1u8d");
			attr(div0, "class", "desktop-nav svelte-jc1u8d");
			attr(a2, "href", "/");
			attr(a2, "class", "logo svelte-jc1u8d");
			attr(button, "id", "open");
			attr(button, "aria-label", "Open mobile navigation");
			attr(div1, "class", "mobile-nav svelte-jc1u8d");
			attr(div2, "class", "section-container svelte-jc1u8d");
			attr(div3, "class", "header-container svelte-jc1u8d");
			attr(header, "class", "svelte-jc1u8d");
			attr(div4, "class", "section");
			attr(div4, "id", "section-a589da36");
		},
		m(target, anchor) {
			insert_hydration(target, div4, anchor);
			append_hydration(div4, header);
			append_hydration(header, div3);
			append_hydration(div3, div2);
			append_hydration(div2, div0);
			append_hydration(div0, a0);
			if (if_block0) if_block0.m(a0, null);
			append_hydration(div0, t0);
			append_hydration(div0, nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(nav, t1);
			append_hydration(nav, a1);
			append_hydration(a1, t2);
			append_hydration(div2, t3);
			append_hydration(div2, div1);
			append_hydration(div1, a2);
			if (if_block1) if_block1.m(a2, null);
			append_hydration(div1, t4);
			append_hydration(div1, button);
			mount_component(icon, button, null);
			append_hydration(div1, t5);
			if (if_block2) if_block2.m(div1, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler*/ ctx[6]);
				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block0) {
				if_block0.p(ctx, dirty);
			} else {
				if (if_block0) if_block0.d(1);
				if_block0 = current_block_type && current_block_type(ctx);

				if (if_block0) {
					if_block0.c();
					if_block0.m(a0, null);
				}
			}

			if (dirty & /*window, site_nav*/ 2) {
				each_value_1 = /*site_nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, t1);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_1.length;
			}

			if ((!current || dirty & /*site_nav_button*/ 4) && t2_value !== (t2_value = /*site_nav_button*/ ctx[2].label + "")) set_data(t2, t2_value);

			if (!current || dirty & /*site_nav_button*/ 4 && a1_href_value !== (a1_href_value = /*site_nav_button*/ ctx[2].url)) {
				attr(a1, "href", a1_href_value);
			}

			if (current_block_type_1 === (current_block_type_1 = select_block_type_1(ctx)) && if_block1) {
				if_block1.p(ctx, dirty);
			} else {
				if (if_block1) if_block1.d(1);
				if_block1 = current_block_type_1 && current_block_type_1(ctx);

				if (if_block1) {
					if_block1.c();
					if_block1.m(a2, null);
				}
			}

			if (/*mobileNavOpen*/ ctx[3]) {
				if (if_block2) {
					if_block2.p(ctx, dirty);

					if (dirty & /*mobileNavOpen*/ 8) {
						transition_in(if_block2, 1);
					}
				} else {
					if_block2 = create_if_block$1(ctx);
					if_block2.c();
					transition_in(if_block2, 1);
					if_block2.m(div1, null);
				}
			} else if (if_block2) {
				group_outros();

				transition_out(if_block2, 1, 1, () => {
					if_block2 = null;
				});

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			transition_in(if_block2);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			transition_out(if_block2);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div4);

			if (if_block0) {
				if_block0.d();
			}

			destroy_each(each_blocks, detaching);

			if (if_block1) {
				if_block1.d();
			}

			destroy_component(icon);
			if (if_block2) if_block2.d();
			mounted = false;
			dispose();
		}
	};
}

function instance$2($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { site_nav_button } = $$props;
	let mobileNavOpen = false;

	function toggleMobileNav() {
		$$invalidate(3, mobileNavOpen = !mobileNavOpen);

		if (mobileNavOpen) {
			document.body.style.overflow = 'hidden';
		} else {
			document.body.style.overflow = 'unset';
		}
	}

	const click_handler = () => toggleMobileNav();
	const click_handler_1 = () => toggleMobileNav();

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(5, favicon = $$props.favicon);
		if ('logo' in $$props) $$invalidate(0, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(1, site_nav = $$props.site_nav);
		if ('site_nav_button' in $$props) $$invalidate(2, site_nav_button = $$props.site_nav_button);
	};

	return [
		logo,
		site_nav,
		site_nav_button,
		mobileNavOpen,
		toggleMobileNav,
		favicon,
		click_handler,
		click_handler_1
	];
}

class Component$2 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$2, create_fragment$2, safe_not_equal, {
			favicon: 5,
			logo: 0,
			site_nav: 1,
			site_nav_button: 2
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$3(ctx) {
	let div3;
	let section;
	let div2;
	let div0;
	let h1;
	let t0;
	let t1;
	let h4;
	let t2;
	let t3;
	let a;
	let t4_value = /*hero_action*/ ctx[2].label + "";
	let t4;
	let a_href_value;
	let t5;
	let div1;
	let img;
	let img_src_value;
	let img_alt_value;
	let t6;
	let lottie_player0;
	let lottie_player0_src_value;
	let t7;
	let lottie_player1;
	let lottie_player1_src_value;

	return {
		c() {
			div3 = element("div");
			section = element("section");
			div2 = element("div");
			div0 = element("div");
			h1 = element("h1");
			t0 = text(/*hero_title_1*/ ctx[0]);
			t1 = space();
			h4 = element("h4");
			t2 = text(/*hero_title_2*/ ctx[1]);
			t3 = space();
			a = element("a");
			t4 = text(t4_value);
			t5 = space();
			div1 = element("div");
			img = element("img");
			t6 = space();
			lottie_player0 = element("lottie-player");
			t7 = space();
			lottie_player1 = element("lottie-player");
			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);
			section = claim_element(div3_nodes, "SECTION", {});
			var section_nodes = children(section);
			div2 = claim_element(section_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h1 = claim_element(div0_nodes, "H1", { class: true });
			var h1_nodes = children(h1);
			t0 = claim_text(h1_nodes, /*hero_title_1*/ ctx[0]);
			h1_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t1 = claim_space(div2_nodes);
			h4 = claim_element(div2_nodes, "H4", { class: true });
			var h4_nodes = children(h4);
			t2 = claim_text(h4_nodes, /*hero_title_2*/ ctx[1]);
			h4_nodes.forEach(detach);
			t3 = claim_space(div2_nodes);
			a = claim_element(div2_nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t4 = claim_text(a_nodes, t4_value);
			a_nodes.forEach(detach);
			t5 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);

			img = claim_element(div1_nodes, "IMG", {
				id: true,
				src: true,
				alt: true,
				class: true
			});

			t6 = claim_space(div1_nodes);

			lottie_player0 = claim_element(div1_nodes, "LOTTIE-PLAYER", {
				autoplay: true,
				loop: true,
				mode: true,
				class: true,
				src: true
			});

			children(lottie_player0).forEach(detach);
			t7 = claim_space(div1_nodes);

			lottie_player1 = claim_element(div1_nodes, "LOTTIE-PLAYER", {
				autoplay: true,
				loop: true,
				mode: true,
				class: true,
				src: true
			});

			children(lottie_player1).forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h1, "class", "svelte-czgz66");
			attr(div0, "class", "hero-text-container1 svelte-czgz66");
			attr(h4, "class", "svelte-czgz66");
			attr(a, "class", "secondary-button svelte-czgz66");
			attr(a, "href", a_href_value = /*hero_action*/ ctx[2].url);
			attr(img, "id", "rewards");
			if (!src_url_equal(img.src, img_src_value = /*hero_image*/ ctx[3].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*hero_image*/ ctx[3].alt);
			attr(img, "class", "svelte-czgz66");
			set_custom_element_data(lottie_player0, "autoplay", "");
			set_custom_element_data(lottie_player0, "loop", "");
			set_custom_element_data(lottie_player0, "mode", "normal");
			set_custom_element_data(lottie_player0, "class", "lottie-2 svelte-czgz66");
			if (!src_url_equal(lottie_player0.src, lottie_player0_src_value = pieChartLottie)) set_custom_element_data(lottie_player0, "src", lottie_player0_src_value);
			set_custom_element_data(lottie_player1, "autoplay", "");
			set_custom_element_data(lottie_player1, "loop", "");
			set_custom_element_data(lottie_player1, "mode", "normal");
			set_custom_element_data(lottie_player1, "class", "lottie-1 svelte-czgz66");
			if (!src_url_equal(lottie_player1.src, lottie_player1_src_value = wideBarChartLottie)) set_custom_element_data(lottie_player1, "src", lottie_player1_src_value);
			attr(div1, "class", "lottie-wrapper svelte-czgz66");
			attr(div2, "class", "header-wrapper svelte-czgz66");
			attr(div3, "class", "section");
			attr(div3, "id", "section-b2c952f8");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, section);
			append_hydration(section, div2);
			append_hydration(div2, div0);
			append_hydration(div0, h1);
			append_hydration(h1, t0);
			append_hydration(div2, t1);
			append_hydration(div2, h4);
			append_hydration(h4, t2);
			append_hydration(div2, t3);
			append_hydration(div2, a);
			append_hydration(a, t4);
			append_hydration(div2, t5);
			append_hydration(div2, div1);
			append_hydration(div1, img);
			append_hydration(div1, t6);
			append_hydration(div1, lottie_player0);
			append_hydration(div1, t7);
			append_hydration(div1, lottie_player1);
		},
		p(ctx, [dirty]) {
			if (dirty & /*hero_title_1*/ 1) set_data(t0, /*hero_title_1*/ ctx[0]);
			if (dirty & /*hero_title_2*/ 2) set_data(t2, /*hero_title_2*/ ctx[1]);
			if (dirty & /*hero_action*/ 4 && t4_value !== (t4_value = /*hero_action*/ ctx[2].label + "")) set_data(t4, t4_value);

			if (dirty & /*hero_action*/ 4 && a_href_value !== (a_href_value = /*hero_action*/ ctx[2].url)) {
				attr(a, "href", a_href_value);
			}

			if (dirty & /*hero_image*/ 8 && !src_url_equal(img.src, img_src_value = /*hero_image*/ ctx[3].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*hero_image*/ 8 && img_alt_value !== (img_alt_value = /*hero_image*/ ctx[3].alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div3);
		}
	};
}

const pieChartLottie = '{"nm":"donat charts","ddd":0,"h":500,"w":500,"meta":{"g":"@lottiefiles/toolkit-js 0.26.1"},"layers":[{"ty":3,"nm":"Null 112","sr":1,"st":0,"op":300,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[50,50,0],"ix":1},"s":{"a":0,"k":[112.5,112.5,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[250,250,0],"ix":2},"r":{"a":1,"k":[{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[0],"t":0},{"s":[99.667],"t":299}]},"sa":{"a":0,"k":0},"o":{"a":0,"k":0,"ix":11}},"ef":[],"ind":1},{"ty":4,"nm":"Shape Layer 3","sr":1,"st":0,"op":300,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[250,250,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":1,"y":0},"i":{"x":0.966,"y":0.706},"s":[0,0,100],"t":4},{"o":{"x":0.03,"y":1.958},"i":{"x":0.486,"y":2.002},"s":[92.051,92.051,100],"t":10.25},{"o":{"x":0.289,"y":2.161},"i":{"x":0.673,"y":1},"s":[111.264,111.264,100],"t":20.25},{"s":[100,100,100],"t":42.75}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[50,50,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[{"ty":0,"mn":"ADBE Fill","nm":"Fill","ix":1,"en":1,"ef":[{"ty":10,"mn":"ADBE Fill-0001","nm":"Fill Mask","ix":1,"v":{"a":0,"k":0,"ix":1}},{"ty":7,"mn":"ADBE Fill-0007","nm":"All Masks","ix":2,"v":{"a":0,"k":0,"ix":2}},{"ty":2,"mn":"ADBE Fill-0002","nm":"Color","ix":3,"v":{"a":1,"k":[{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[0.1765,0.1765,0.1765],"t":0},{"s":[0.1765,0.1765,0.1765],"t":299}]}},{"ty":7,"mn":"ADBE Fill-0006","nm":"Invert","ix":4,"v":{"a":0,"k":0,"ix":4}},{"ty":0,"mn":"ADBE Fill-0003","nm":"Horizontal Feather","ix":5,"v":{"a":0,"k":0,"ix":5}},{"ty":0,"mn":"ADBE Fill-0004","nm":"Vertical Feather","ix":6,"v":{"a":0,"k":0,"ix":6}},{"ty":0,"mn":"ADBE Fill-0005","nm":"Opacity","ix":7,"v":{"a":0,"k":1,"ix":7}}]}],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 3","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[0.893,-2.35],[21.511,0],[6.307,2.85],[1.791,-1.794],[0,0],[-3.27,-2.102],[-19.769,0],[-9.802,44.709],[3.902,0]],"o":[[-2.517,0],[-7.216,19.011],[-7.361,0],[-2.312,-1.043],[0,0],[-2.749,2.749],[15.509,9.97],[47.611,0],[0.836,-3.811],[0,0]],"v":[[32.454,-42.86],[26.811,-38.944],[-20.308,-6.381],[-40.97,-10.822],[-47.779,-9.62],[-75.086,17.688],[-74.024,27.097],[-20.308,42.859],[76.999,-35.421],[71.107,-42.86]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.8353,0.8431,0.9373],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[271.12,305.813],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":2,"parent":1},{"ty":4,"nm":"Shape Layer 2","sr":1,"st":0,"op":300,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[250,250,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":1,"y":0},"i":{"x":0.966,"y":0.706},"s":[0,0,100],"t":2},{"o":{"x":0.03,"y":1.958},"i":{"x":0.486,"y":2.002},"s":[92.051,92.051,100],"t":8.25},{"o":{"x":0.289,"y":2.161},"i":{"x":0.673,"y":1},"s":[111.264,111.264,100],"t":18.25},{"s":[100,100,100],"t":40.75}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[50,50,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[{"ty":0,"mn":"ADBE Fill","nm":"Fill","ix":1,"en":1,"ef":[{"ty":10,"mn":"ADBE Fill-0001","nm":"Fill Mask","ix":1,"v":{"a":0,"k":0,"ix":1}},{"ty":7,"mn":"ADBE Fill-0007","nm":"All Masks","ix":2,"v":{"a":0,"k":0,"ix":2}},{"ty":2,"mn":"ADBE Fill-0002","nm":"Color","ix":3,"v":{"a":1,"k":[{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[0.1765,0.1765,0.1765],"t":0},{"s":[0.1765,0.1765,0.1765],"t":299}]}},{"ty":7,"mn":"ADBE Fill-0006","nm":"Invert","ix":4,"v":{"a":0,"k":0,"ix":4}},{"ty":0,"mn":"ADBE Fill-0003","nm":"Horizontal Feather","ix":5,"v":{"a":0,"k":0,"ix":5}},{"ty":0,"mn":"ADBE Fill-0004","nm":"Vertical Feather","ix":6,"v":{"a":0,"k":0,"ix":6}},{"ty":0,"mn":"ADBE Fill-0005","nm":"Opacity","ix":7,"v":{"a":0,"k":1,"ix":7}}]}],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 2","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[1.043,2.311],[0,7.36],[-19.013,7.218],[0,2.513],[0,0],[3.811,-0.839],[0,-47.607],[-9.968,-15.509],[-2.749,2.749]],"o":[[1.793,-1.794],[-2.849,-6.307],[0,-21.508],[2.35,-0.89],[0,0],[0,-3.901],[-44.709,9.801],[0,19.768],[2.103,3.272],[0,0]],"v":[[9.622,47.781],[10.824,40.969],[6.38,20.307],[38.945,-26.815],[42.859,-32.453],[42.859,-71.106],[35.421,-76.997],[-42.859,20.307],[-27.098,74.023],[-17.686,75.088]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.8353,0.8431,0.9373],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[194.038,228.731],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":3,"parent":1},{"ty":4,"nm":"Shape Layer 1","sr":1,"st":0,"op":300,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[250,250,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":1,"y":0},"i":{"x":0.966,"y":0.706},"s":[0,0,100],"t":0},{"o":{"x":0.03,"y":1.958},"i":{"x":0.486,"y":2.002},"s":[92.051,92.051,100],"t":6.25},{"o":{"x":0.289,"y":2.161},"i":{"x":0.673,"y":1},"s":[111.264,111.264,100],"t":16.25},{"s":[100,100,100],"t":38.75}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[50,50,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[{"ty":0,"mn":"ADBE Fill","nm":"Fill","ix":1,"en":1,"ef":[{"ty":10,"mn":"ADBE Fill-0001","nm":"Fill Mask","ix":1,"v":{"a":0,"k":0,"ix":1}},{"ty":7,"mn":"ADBE Fill-0007","nm":"All Masks","ix":2,"v":{"a":0,"k":0,"ix":2}},{"ty":2,"mn":"ADBE Fill-0002","nm":"Color","ix":3,"v":{"a":1,"k":[{"o":{"x":0,"y":0},"i":{"x":1,"y":1},"s":[0.102,0.7373,0.6118],"t":0},{"s":[0.102,0.7373,0.6118],"t":299}]}},{"ty":7,"mn":"ADBE Fill-0006","nm":"Invert","ix":4,"v":{"a":0,"k":0,"ix":4}},{"ty":0,"mn":"ADBE Fill-0003","nm":"Horizontal Feather","ix":5,"v":{"a":0,"k":0,"ix":5}},{"ty":0,"mn":"ADBE Fill-0004","nm":"Vertical Feather","ix":6,"v":{"a":0,"k":0,"ix":6}},{"ty":0,"mn":"ADBE Fill-0005","nm":"Opacity","ix":7,"v":{"a":0,"k":1,"ix":7}}]}],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[-2.36,-0.897],[-5.112,-13.443],[-2.523,0],[0,0],[0.834,3.811],[37.822,8.292],[0,-3.901],[0,0]],"o":[[13.44,5.109],[0.896,2.358],[0,0],[3.901,0],[-8.296,-37.82],[-3.814,-0.836],[0,0],[0,2.523]],"v":[[-38.173,8.916],[-8.916,38.174],[-3.266,42.113],[35.388,42.113],[41.279,34.671],[-34.671,-41.277],[-42.112,-35.387],[-42.112,3.266]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0.3098,0.6392],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[306.84,193.01],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":4,"parent":1}],"v":"5.9.6","fr":30,"op":300,"ip":0,"assets":[]}';
const wideBarChartLottie = '{"nm":"191","ddd":0,"h":1080,"w":1920,"meta":{"g":"@lottiefiles/toolkit-js 0.26.1"},"layers":[{"ty":4,"nm":"Shape Layer 24","sr":1,"st":0,"op":751,"ip":0,"hd":true,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-776.125,204.625,0],"ix":1},"s":{"a":0,"k":[64,64,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[1758.375,746.625,0],"ix":2},"r":{"a":0,"k":45,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"rc","bm":0,"hd":false,"mn":"ADBE Vector Shape - Rect","nm":"Rectangle Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"r":{"a":0,"k":6.7,"ix":4},"s":{"a":0,"k":[41.75,41.75],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":0,"ix":5},"c":{"a":0,"k":[1,1,1],"ix":3}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.6863,0.8,0.2627],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-776.125,204.625],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":1},{"ty":4,"nm":"Shape Layer 23","sr":1,"st":0,"op":751,"ip":0,"hd":true,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-776.125,204.625,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[1758.375,746.625,0],"ix":2},"r":{"a":0,"k":45,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"rc","bm":0,"hd":false,"mn":"ADBE Vector Shape - Rect","nm":"Rectangle Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"r":{"a":0,"k":6.7,"ix":4},"s":{"a":0,"k":[41.75,41.75],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":0,"ix":5},"c":{"a":0,"k":[1,1,1],"ix":3}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,1,1],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-776.125,204.625],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":2},{"ty":4,"nm":"Shape Layer 22","sr":1,"st":0,"op":751,"ip":0,"hd":true,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-776.125,204.625,0],"ix":1},"s":{"a":0,"k":[64,64,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[1617.875,746.625,0],"ix":2},"r":{"a":0,"k":45,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"rc","bm":0,"hd":false,"mn":"ADBE Vector Shape - Rect","nm":"Rectangle Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"r":{"a":0,"k":6.7,"ix":4},"s":{"a":0,"k":[41.75,41.75],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":0,"ix":5},"c":{"a":0,"k":[1,1,1],"ix":3}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.2392,0.7804,0.4196],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-776.125,204.625],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":3},{"ty":4,"nm":"Shape Layer 21","sr":1,"st":0,"op":751,"ip":0,"hd":true,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-776.125,204.625,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[1617.875,746.625,0],"ix":2},"r":{"a":0,"k":45,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"rc","bm":0,"hd":false,"mn":"ADBE Vector Shape - Rect","nm":"Rectangle Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"r":{"a":0,"k":6.7,"ix":4},"s":{"a":0,"k":[41.75,41.75],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":0,"ix":5},"c":{"a":0,"k":[1,1,1],"ix":3}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,1,1],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-776.125,204.625],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":4},{"ty":4,"nm":"Shape Layer 20","sr":1,"st":0,"op":751,"ip":0,"hd":true,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-776.125,204.625,0],"ix":1},"s":{"a":0,"k":[64,64,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[1475.125,746.625,0],"ix":2},"r":{"a":0,"k":45,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"rc","bm":0,"hd":false,"mn":"ADBE Vector Shape - Rect","nm":"Rectangle Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"r":{"a":0,"k":6.7,"ix":4},"s":{"a":0,"k":[41.75,41.75],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":0,"ix":5},"c":{"a":0,"k":[1,1,1],"ix":3}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.349,0.7725,0.7059],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-776.125,204.625],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":5},{"ty":4,"nm":"Shape Layer 19","sr":1,"st":0,"op":751,"ip":0,"hd":true,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-776.125,204.625,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[1475.125,746.625,0],"ix":2},"r":{"a":0,"k":45,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"rc","bm":0,"hd":false,"mn":"ADBE Vector Shape - Rect","nm":"Rectangle Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"r":{"a":0,"k":6.7,"ix":4},"s":{"a":0,"k":[41.75,41.75],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":0,"ix":5},"c":{"a":0,"k":[1,1,1],"ix":3}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,1,1],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-776.125,204.625],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":6},{"ty":4,"nm":"Shape Layer 38","sr":1,"st":0,"op":751,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-770.5,207,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[100,449.4,100],"t":0},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[100,490.4,100],"t":112},{"s":[100,449.4,100],"t":247}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[1759.5,747,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"rc","bm":0,"hd":false,"mn":"ADBE Vector Shape - Rect","nm":"Rectangle Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"r":{"a":0,"k":0,"ix":4},"s":{"a":0,"k":[107.5,91.75],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":0,"ix":5},"c":{"a":0,"k":[1,1,1],"ix":3}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0.3098,0.6392],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-771,161.125],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":7},{"ty":4,"nm":"Shape Layer 37","sr":1,"st":0,"op":751,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-770.5,207,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[100,218.4,100],"t":0},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[100,243.4,100],"t":56},{"s":[100,218.4,100],"t":117}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[1618,747,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"rc","bm":0,"hd":false,"mn":"ADBE Vector Shape - Rect","nm":"Rectangle Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"r":{"a":0,"k":0,"ix":4},"s":{"a":0,"k":[107.5,91.75],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":0,"ix":5},"c":{"a":0,"k":[1,1,1],"ix":3}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0,0,0],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-771,161.125],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":8},{"ty":4,"nm":"Shape Layer 36","sr":1,"st":0,"op":751,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-770.5,207,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[100,333.4,100],"t":0},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[100,366.4,100],"t":77},{"s":[100,333.4,100],"t":166}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[1475,747,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"rc","bm":0,"hd":false,"mn":"ADBE Vector Shape - Rect","nm":"Rectangle Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"r":{"a":0,"k":0,"ix":4},"s":{"a":0,"k":[107.5,91.75],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":0,"ix":5},"c":{"a":0,"k":[1,1,1],"ix":3}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9647,0.898,0],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-771,161.125],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":9},{"ty":4,"nm":"Shape Layer 35","sr":1,"st":0,"op":751,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-770.5,207,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[100,103.4,100],"t":0},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[100,130.4,100],"t":76},{"s":[100,103.4,100],"t":154}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[1337,747,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"rc","bm":0,"hd":false,"mn":"ADBE Vector Shape - Rect","nm":"Rectangle Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"r":{"a":0,"k":0,"ix":4},"s":{"a":0,"k":[107.5,91.75],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":0,"ix":5},"c":{"a":0,"k":[1,1,1],"ix":3}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0.3098,0.6392],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-771,161.125],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":10},{"ty":4,"nm":"Shape Layer 34","sr":1,"st":0,"op":751,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-770.5,207,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[100,217.4,100],"t":0},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[100,256.4,100],"t":67},{"s":[100,217.4,100],"t":140}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[1192,747,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"rc","bm":0,"hd":false,"mn":"ADBE Vector Shape - Rect","nm":"Rectangle Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"r":{"a":0,"k":0,"ix":4},"s":{"a":0,"k":[107.5,91.75],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":0,"ix":5},"c":{"a":0,"k":[1,1,1],"ix":3}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0,0,0],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-771,161.125],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":11},{"ty":4,"nm":"Shape Layer 33","sr":1,"st":0,"op":751,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-770.5,207,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[100,347.4,100],"t":0},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[100,316.4,100],"t":80},{"s":[100,347.4,100],"t":154}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[1050.5,747,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"rc","bm":0,"hd":false,"mn":"ADBE Vector Shape - Rect","nm":"Rectangle Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"r":{"a":0,"k":0,"ix":4},"s":{"a":0,"k":[107.5,91.75],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":0,"ix":5},"c":{"a":0,"k":[1,1,1],"ix":3}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9647,0.898,0],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-771,161.125],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":12},{"ty":4,"nm":"Shape Layer 32","sr":1,"st":0,"op":751,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-770.5,207,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[100,247.4,100],"t":0},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[100,199.4,100],"t":87},{"s":[100,247.4,100],"t":180}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[907,747,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"rc","bm":0,"hd":false,"mn":"ADBE Vector Shape - Rect","nm":"Rectangle Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"r":{"a":0,"k":0,"ix":4},"s":{"a":0,"k":[107.5,91.75],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":0,"ix":5},"c":{"a":0,"k":[1,1,1],"ix":3}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0.3098,0.6392],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-771,161.125],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":13},{"ty":4,"nm":"Shape Layer 31","sr":1,"st":0,"op":751,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-770.5,207,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[100,98.4,100],"t":0},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[100,141.4,100],"t":60},{"s":[100,98.4,100],"t":127}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[762,747,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"rc","bm":0,"hd":false,"mn":"ADBE Vector Shape - Rect","nm":"Rectangle Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"r":{"a":0,"k":0,"ix":4},"s":{"a":0,"k":[107.5,91.75],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":0,"ix":5},"c":{"a":0,"k":[1,1,1],"ix":3}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0,0,0],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-771,161.125],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":14},{"ty":4,"nm":"Shape Layer 30","sr":1,"st":0,"op":751,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-770.5,207,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[100,299.4,100],"t":0},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[100,361.4,100],"t":75},{"s":[100,299.4,100],"t":154}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[613.5,747,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"rc","bm":0,"hd":false,"mn":"ADBE Vector Shape - Rect","nm":"Rectangle Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"r":{"a":0,"k":0,"ix":4},"s":{"a":0,"k":[107.5,91.75],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":0,"ix":5},"c":{"a":0,"k":[1,1,1],"ix":3}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9647,0.898,0],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-771,161.125],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":15},{"ty":4,"nm":"Shape Layer 29","sr":1,"st":0,"op":751,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-770.5,207,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[100,216.4,100],"t":0},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[100,271.4,100],"t":63},{"s":[100,216.4,100],"t":131}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[473.5,747,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"rc","bm":0,"hd":false,"mn":"ADBE Vector Shape - Rect","nm":"Rectangle Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"r":{"a":0,"k":0,"ix":4},"s":{"a":0,"k":[107.5,91.75],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":0,"ix":5},"c":{"a":0,"k":[1,1,1],"ix":3}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0.3098,0.6392],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-771,161.125],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":16},{"ty":4,"nm":"Shape Layer 28","sr":1,"st":0,"op":751,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-770.5,207,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[100,216.4,100],"t":0},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[100,257.4,100],"t":34},{"s":[100,216.4,100],"t":74}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[330.5,747,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"rc","bm":0,"hd":false,"mn":"ADBE Vector Shape - Rect","nm":"Rectangle Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"r":{"a":0,"k":0,"ix":4},"s":{"a":0,"k":[107.5,91.75],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":0,"ix":5},"c":{"a":0,"k":[1,1,1],"ix":3}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0,0,0],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-771,161.125],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":17},{"ty":4,"nm":"Shape Layer 27","sr":1,"st":0,"op":751,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-770.5,207,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[100,67,100],"t":0},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[100,128,100],"t":50},{"s":[100,67,100],"t":100}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[189.5,747,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"rc","bm":0,"hd":false,"mn":"ADBE Vector Shape - Rect","nm":"Rectangle Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"r":{"a":0,"k":0,"ix":4},"s":{"a":0,"k":[107.5,91.75],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":0,"ix":5},"c":{"a":0,"k":[1,1,1],"ix":3}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9647,0.898,0],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-771,161.125],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":18}],"v":"5.8.1","fr":25,"op":751,"ip":0,"fonts":{"list":[{"ascent":71.6088159177452,"fClass":"","fFamily":"Arial","fStyle":"Bold","fName":"Arial-BoldMT","fPath":"","fWeight":"","origin":0}]},"chars":[{"ch":"2","fFamily":"Arial","size":45,"style":"Bold","w":55.62,"data":{"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"2","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"2","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[-1.156,1.302],[-4.33,3.972],[-1.66,2.116],[-1.156,2.914],[0,3.223],[4.036,3.809],[7.063,0],[4.297,-3.288],[0.813,-7.552],[0,0],[-1.693,1.726],[-2.865,0],[-1.644,-1.643],[0,-3.059],[1.888,-2.832],[6.184,-5.762],[2.604,-4.313],[0.52,-4.817],[0,0],[0,0]],"o":[[0.716,-1.237],[1.155,-1.302],[4.329,-3.971],[2.506,-3.19],[1.155,-2.913],[0,-5.664],[-4.037,-3.809],[-6.445,0],[-4.297,3.288],[0,0],[0.26,-4.004],[1.692,-1.725],[2.897,0],[1.643,1.644],[0,2.767],[-1.4,2.051],[-7.683,7.129],[-2.605,4.314],[0,0],[0,0],[0,0]],"v":[[23.34,-12.744],[26.147,-16.553],[34.375,-24.463],[43.359,-33.594],[48.853,-42.749],[50.586,-51.953],[44.531,-66.162],[27.881,-71.875],[11.768,-66.943],[4.102,-50.684],[17.773,-49.316],[20.703,-57.91],[27.539,-60.498],[34.351,-58.032],[36.816,-50.977],[33.984,-42.578],[22.607,-30.859],[7.178,-13.696],[2.49,0],[50.586,0],[50.586,-12.744]]},"ix":2}}]}]}},{"ch":"5","fFamily":"Arial","size":45,"style":"Bold","w":55.62,"data":{"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"5","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"5","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[-4.167,-3.548],[-6.609,0],[-4.655,6.316],[0,5.892],[4.231,4.427],[6.087,0],[3.059,-1.53],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[-3.939,0],[-1.97,-2.197],[0,-4.395],[1.985,-2.327],[2.864,0],[1.92,1.807],[0.391,3.093],[0,0]],"o":[[4.166,3.548],[8.268,0],[3.418,-4.622],[0,-7.063],[-4.232,-4.427],[-3.191,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[3.125,-3.483],[3.157,0],[1.969,2.197],[0,4.688],[-1.986,2.328],[-2.507,0],[-1.921,-1.807],[0,0],[0.813,5.99]],"v":[[11.914,-4.102],[28.076,1.221],[47.461,-8.252],[52.588,-24.023],[46.24,-41.26],[30.762,-47.9],[21.387,-45.605],[23.535,-57.764],[49.414,-57.764],[49.414,-70.605],[13.135,-70.605],[6.104,-33.35],[17.236,-31.738],[27.832,-36.963],[35.522,-33.667],[38.477,-23.779],[35.498,-13.257],[28.223,-9.766],[21.582,-12.476],[18.115,-19.824],[4.443,-18.408]]},"ix":2}}]}]}},{"ch":"0","fFamily":"Arial","size":45,"style":"Bold","w":55.62,"data":{"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"0","ix":1,"cix":2,"np":5,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"0","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[3.873,-4.883],[0,-13.477],[-4.265,-5.354],[-6.966,0],[-3.874,4.883],[0,13.542],[4.655,5.859],[6.934,0]],"o":[[-4.688,5.925],[0,13.737],[4.264,5.355],[6.934,0],[4.688,-5.924],[0,-13.574],[-3.906,-4.948],[-6.934,0]],"v":[[11.23,-64.551],[4.199,-35.449],[10.596,-6.812],[27.441,1.221],[43.652,-6.104],[50.684,-35.303],[43.701,-64.453],[27.441,-71.875]]},"ix":2}},{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"0","ix":2,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[-1.286,-1.057],[-0.847,-3.141],[0,-8.398],[0.944,-3.516],[1.302,-1.057],[1.66,0],[1.286,1.042],[0.846,3.142],[0,8.398],[-0.945,3.548],[-1.302,1.058],[-1.66,0]],"o":[[1.286,1.058],[0.846,3.142],[0,8.398],[-0.716,2.734],[-1.302,1.058],[-1.66,0],[-1.286,-1.041],[-0.847,-3.141],[0,-8.398],[0.716,-2.734],[1.302,-1.057],[1.66,0]],"v":[[31.86,-58.911],[35.059,-52.612],[36.328,-35.303],[34.912,-17.432],[31.885,-11.743],[27.441,-10.156],[23.022,-11.719],[19.824,-17.993],[18.555,-35.303],[19.971,-53.223],[22.998,-58.911],[27.441,-60.498]]},"ix":2}}]}]}},{"ch":"7","fFamily":"Arial","size":45,"style":"Bold","w":55.62,"data":{"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"7","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"7","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[3.857,-10.286],[0.227,-9.895],[0,0],[-2.1,8.025],[-4.004,7.129],[-3.874,3.809],[0,0],[0,0],[0,0]],"o":[[-6.445,8.105],[-3.857,10.287],[0,0],[-0.033,-6.315],[2.1,-8.024],[4.004,-7.129],[0,0],[0,0],[0,0],[0,0]],"v":[[35.449,-57.861],[19.995,-30.273],[13.867,0],[27.1,0],[30.2,-21.509],[39.355,-44.238],[51.172,-60.645],[51.172,-70.605],[4.248,-70.605],[4.248,-57.861]]},"ix":2}}]}]}},{"ch":"1","fFamily":"Arial","size":45,"style":"Bold","w":50.1,"data":{"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"1","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[0,0],[4.199,-3.271],[3.58,-1.172],[0,0],[-5.013,4.688],[0,0],[0,0]],"o":[[0,0],[-1.563,4.362],[-4.199,3.271],[0,0],[6.803,-2.246],[0,0],[0,0],[0,0]],"v":[[39.355,-71.875],[28.223,-71.875],[19.58,-60.425],[7.91,-53.76],[7.91,-41.309],[25.635,-51.709],[25.635,0],[39.355,0]]},"ix":2}}]}]}}],"assets":[]}';

function instance$3($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { hero_title_1 } = $$props;
	let { hero_title_2 } = $$props;
	let { hero_action } = $$props;
	let { hero_image } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(4, favicon = $$props.favicon);
		if ('hero_title_1' in $$props) $$invalidate(0, hero_title_1 = $$props.hero_title_1);
		if ('hero_title_2' in $$props) $$invalidate(1, hero_title_2 = $$props.hero_title_2);
		if ('hero_action' in $$props) $$invalidate(2, hero_action = $$props.hero_action);
		if ('hero_image' in $$props) $$invalidate(3, hero_image = $$props.hero_image);
	};

	return [hero_title_1, hero_title_2, hero_action, hero_image, favicon];
}

class Component$3 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$3, create_fragment$3, safe_not_equal, {
			favicon: 4,
			hero_title_1: 0,
			hero_title_2: 1,
			hero_action: 2,
			hero_image: 3
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$4(ctx) {
	let div8;
	let div7;
	let div6;
	let div5;
	let h3;
	let t0;
	let t1;
	let p0;
	let t2;
	let t3;
	let section;
	let div0;
	let h60;
	let t4;
	let t5;
	let p1;
	let t6;
	let t7;
	let div1;
	let h61;
	let t8;
	let t9;
	let p2;
	let t10;
	let t11;
	let div2;
	let h62;
	let t12;
	let t13;
	let p3;
	let t14;
	let t15;
	let div3;
	let h63;
	let t16;
	let t17;
	let p4;
	let t18;
	let t19;
	let div4;
	let h64;
	let t20;
	let t21;
	let p5;
	let t22;

	return {
		c() {
			div8 = element("div");
			div7 = element("div");
			div6 = element("div");
			div5 = element("div");
			h3 = element("h3");
			t0 = text(/*content_title*/ ctx[0]);
			t1 = space();
			p0 = element("p");
			t2 = text(/*content_description*/ ctx[1]);
			t3 = space();
			section = element("section");
			div0 = element("div");
			h60 = element("h6");
			t4 = text(/*content_tag_1*/ ctx[2]);
			t5 = space();
			p1 = element("p");
			t6 = text(/*content_paragraph_1*/ ctx[3]);
			t7 = space();
			div1 = element("div");
			h61 = element("h6");
			t8 = text(/*content_tag_2*/ ctx[4]);
			t9 = space();
			p2 = element("p");
			t10 = text(/*content_paragraph_2*/ ctx[5]);
			t11 = space();
			div2 = element("div");
			h62 = element("h6");
			t12 = text(/*content_tag_3*/ ctx[6]);
			t13 = space();
			p3 = element("p");
			t14 = text(/*content_paragraph_3*/ ctx[7]);
			t15 = space();
			div3 = element("div");
			h63 = element("h6");
			t16 = text(/*content_tag_4*/ ctx[8]);
			t17 = space();
			p4 = element("p");
			t18 = text(/*content_paragraph_4*/ ctx[9]);
			t19 = space();
			div4 = element("div");
			h64 = element("h6");
			t20 = text(/*content_tag_5*/ ctx[10]);
			t21 = space();
			p5 = element("p");
			t22 = text(/*content_paragraph_5*/ ctx[11]);
			this.h();
		},
		l(nodes) {
			div8 = claim_element(nodes, "DIV", { class: true, id: true });
			var div8_nodes = children(div8);
			div7 = claim_element(div8_nodes, "DIV", { class: true });
			var div7_nodes = children(div7);
			div6 = claim_element(div7_nodes, "DIV", { class: true });
			var div6_nodes = children(div6);
			div5 = claim_element(div6_nodes, "DIV", { class: true });
			var div5_nodes = children(div5);
			h3 = claim_element(div5_nodes, "H3", {});
			var h3_nodes = children(h3);
			t0 = claim_text(h3_nodes, /*content_title*/ ctx[0]);
			h3_nodes.forEach(detach);
			t1 = claim_space(div5_nodes);
			p0 = claim_element(div5_nodes, "P", { id: true, class: true });
			var p0_nodes = children(p0);
			t2 = claim_text(p0_nodes, /*content_description*/ ctx[1]);
			p0_nodes.forEach(detach);
			t3 = claim_space(div5_nodes);
			section = claim_element(div5_nodes, "SECTION", {});
			var section_nodes = children(section);
			div0 = claim_element(section_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h60 = claim_element(div0_nodes, "H6", { class: true });
			var h60_nodes = children(h60);
			t4 = claim_text(h60_nodes, /*content_tag_1*/ ctx[2]);
			h60_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t5 = claim_space(section_nodes);
			p1 = claim_element(section_nodes, "P", { class: true });
			var p1_nodes = children(p1);
			t6 = claim_text(p1_nodes, /*content_paragraph_1*/ ctx[3]);
			p1_nodes.forEach(detach);
			t7 = claim_space(section_nodes);
			div1 = claim_element(section_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h61 = claim_element(div1_nodes, "H6", { class: true });
			var h61_nodes = children(h61);
			t8 = claim_text(h61_nodes, /*content_tag_2*/ ctx[4]);
			h61_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			t9 = claim_space(section_nodes);
			p2 = claim_element(section_nodes, "P", { class: true });
			var p2_nodes = children(p2);
			t10 = claim_text(p2_nodes, /*content_paragraph_2*/ ctx[5]);
			p2_nodes.forEach(detach);
			t11 = claim_space(section_nodes);
			div2 = claim_element(section_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			h62 = claim_element(div2_nodes, "H6", { class: true });
			var h62_nodes = children(h62);
			t12 = claim_text(h62_nodes, /*content_tag_3*/ ctx[6]);
			h62_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t13 = claim_space(section_nodes);
			p3 = claim_element(section_nodes, "P", { class: true });
			var p3_nodes = children(p3);
			t14 = claim_text(p3_nodes, /*content_paragraph_3*/ ctx[7]);
			p3_nodes.forEach(detach);
			t15 = claim_space(section_nodes);
			div3 = claim_element(section_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			h63 = claim_element(div3_nodes, "H6", { class: true });
			var h63_nodes = children(h63);
			t16 = claim_text(h63_nodes, /*content_tag_4*/ ctx[8]);
			h63_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			t17 = claim_space(section_nodes);
			p4 = claim_element(section_nodes, "P", { class: true });
			var p4_nodes = children(p4);
			t18 = claim_text(p4_nodes, /*content_paragraph_4*/ ctx[9]);
			p4_nodes.forEach(detach);
			t19 = claim_space(section_nodes);
			div4 = claim_element(section_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);
			h64 = claim_element(div4_nodes, "H6", { class: true });
			var h64_nodes = children(h64);
			t20 = claim_text(h64_nodes, /*content_tag_5*/ ctx[10]);
			h64_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			t21 = claim_space(section_nodes);
			p5 = claim_element(section_nodes, "P", { class: true });
			var p5_nodes = children(p5);
			t22 = claim_text(p5_nodes, /*content_paragraph_5*/ ctx[11]);
			p5_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div5_nodes.forEach(detach);
			div6_nodes.forEach(detach);
			div7_nodes.forEach(detach);
			div8_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(p0, "id", "content-paragraph-1");
			attr(p0, "class", "p-large svelte-iy3roc");
			attr(h60, "class", "h700");
			attr(div0, "class", "tag-pink-large svelte-iy3roc");
			attr(p1, "class", "p-large");
			attr(h61, "class", "h700");
			attr(div1, "class", "tag-pink-large svelte-iy3roc");
			attr(p2, "class", "p-large");
			attr(h62, "class", "h700");
			attr(div2, "class", "tag-pink-large svelte-iy3roc");
			attr(p3, "class", "p-large");
			attr(h63, "class", "h700");
			attr(div3, "class", "tag-pink-large svelte-iy3roc");
			attr(p4, "class", "p-large");
			attr(h64, "class", "h700");
			attr(div4, "class", "tag-pink-large svelte-iy3roc");
			attr(p5, "class", "p-large");
			attr(div5, "class", "section-container content svelte-iy3roc");
			attr(div6, "class", "wrapper svelte-iy3roc");
			attr(div7, "class", "container svelte-iy3roc");
			attr(div8, "class", "section");
			attr(div8, "id", "section-4a6fb994");
		},
		m(target, anchor) {
			insert_hydration(target, div8, anchor);
			append_hydration(div8, div7);
			append_hydration(div7, div6);
			append_hydration(div6, div5);
			append_hydration(div5, h3);
			append_hydration(h3, t0);
			append_hydration(div5, t1);
			append_hydration(div5, p0);
			append_hydration(p0, t2);
			append_hydration(div5, t3);
			append_hydration(div5, section);
			append_hydration(section, div0);
			append_hydration(div0, h60);
			append_hydration(h60, t4);
			append_hydration(section, t5);
			append_hydration(section, p1);
			append_hydration(p1, t6);
			append_hydration(section, t7);
			append_hydration(section, div1);
			append_hydration(div1, h61);
			append_hydration(h61, t8);
			append_hydration(section, t9);
			append_hydration(section, p2);
			append_hydration(p2, t10);
			append_hydration(section, t11);
			append_hydration(section, div2);
			append_hydration(div2, h62);
			append_hydration(h62, t12);
			append_hydration(section, t13);
			append_hydration(section, p3);
			append_hydration(p3, t14);
			append_hydration(section, t15);
			append_hydration(section, div3);
			append_hydration(div3, h63);
			append_hydration(h63, t16);
			append_hydration(section, t17);
			append_hydration(section, p4);
			append_hydration(p4, t18);
			append_hydration(section, t19);
			append_hydration(section, div4);
			append_hydration(div4, h64);
			append_hydration(h64, t20);
			append_hydration(section, t21);
			append_hydration(section, p5);
			append_hydration(p5, t22);
		},
		p(ctx, [dirty]) {
			if (dirty & /*content_title*/ 1) set_data(t0, /*content_title*/ ctx[0]);
			if (dirty & /*content_description*/ 2) set_data(t2, /*content_description*/ ctx[1]);
			if (dirty & /*content_tag_1*/ 4) set_data(t4, /*content_tag_1*/ ctx[2]);
			if (dirty & /*content_paragraph_1*/ 8) set_data(t6, /*content_paragraph_1*/ ctx[3]);
			if (dirty & /*content_tag_2*/ 16) set_data(t8, /*content_tag_2*/ ctx[4]);
			if (dirty & /*content_paragraph_2*/ 32) set_data(t10, /*content_paragraph_2*/ ctx[5]);
			if (dirty & /*content_tag_3*/ 64) set_data(t12, /*content_tag_3*/ ctx[6]);
			if (dirty & /*content_paragraph_3*/ 128) set_data(t14, /*content_paragraph_3*/ ctx[7]);
			if (dirty & /*content_tag_4*/ 256) set_data(t16, /*content_tag_4*/ ctx[8]);
			if (dirty & /*content_paragraph_4*/ 512) set_data(t18, /*content_paragraph_4*/ ctx[9]);
			if (dirty & /*content_tag_5*/ 1024) set_data(t20, /*content_tag_5*/ ctx[10]);
			if (dirty & /*content_paragraph_5*/ 2048) set_data(t22, /*content_paragraph_5*/ ctx[11]);
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div8);
		}
	};
}

function instance$4($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { content_title } = $$props;
	let { content_description } = $$props;
	let { content_tag_1 } = $$props;
	let { content_paragraph_1 } = $$props;
	let { content_tag_2 } = $$props;
	let { content_paragraph_2 } = $$props;
	let { content_tag_3 } = $$props;
	let { content_paragraph_3 } = $$props;
	let { content_tag_4 } = $$props;
	let { content_paragraph_4 } = $$props;
	let { content_tag_5 } = $$props;
	let { content_paragraph_5 } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(12, favicon = $$props.favicon);
		if ('content_title' in $$props) $$invalidate(0, content_title = $$props.content_title);
		if ('content_description' in $$props) $$invalidate(1, content_description = $$props.content_description);
		if ('content_tag_1' in $$props) $$invalidate(2, content_tag_1 = $$props.content_tag_1);
		if ('content_paragraph_1' in $$props) $$invalidate(3, content_paragraph_1 = $$props.content_paragraph_1);
		if ('content_tag_2' in $$props) $$invalidate(4, content_tag_2 = $$props.content_tag_2);
		if ('content_paragraph_2' in $$props) $$invalidate(5, content_paragraph_2 = $$props.content_paragraph_2);
		if ('content_tag_3' in $$props) $$invalidate(6, content_tag_3 = $$props.content_tag_3);
		if ('content_paragraph_3' in $$props) $$invalidate(7, content_paragraph_3 = $$props.content_paragraph_3);
		if ('content_tag_4' in $$props) $$invalidate(8, content_tag_4 = $$props.content_tag_4);
		if ('content_paragraph_4' in $$props) $$invalidate(9, content_paragraph_4 = $$props.content_paragraph_4);
		if ('content_tag_5' in $$props) $$invalidate(10, content_tag_5 = $$props.content_tag_5);
		if ('content_paragraph_5' in $$props) $$invalidate(11, content_paragraph_5 = $$props.content_paragraph_5);
	};

	return [
		content_title,
		content_description,
		content_tag_1,
		content_paragraph_1,
		content_tag_2,
		content_paragraph_2,
		content_tag_3,
		content_paragraph_3,
		content_tag_4,
		content_paragraph_4,
		content_tag_5,
		content_paragraph_5,
		favicon
	];
}

class Component$4 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$4, create_fragment$4, safe_not_equal, {
			favicon: 12,
			content_title: 0,
			content_description: 1,
			content_tag_1: 2,
			content_paragraph_1: 3,
			content_tag_2: 4,
			content_paragraph_2: 5,
			content_tag_3: 6,
			content_paragraph_3: 7,
			content_tag_4: 8,
			content_paragraph_4: 9,
			content_tag_5: 10,
			content_paragraph_5: 11
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$5(ctx) {
	let div13;
	let div12;
	let div11;
	let div10;
	let h3;
	let t0;
	let t1;
	let p0;
	let t2;
	let t3;
	let section0;
	let div0;
	let h60;
	let t4_value = /*content_1*/ ctx[2].tag + "";
	let t4;
	let t5;
	let h61;
	let t6_value = /*content_1*/ ctx[2].title + "";
	let t6;
	let t7;
	let p1;
	let t8_value = /*content_1*/ ctx[2].description + "";
	let t8;
	let t9;
	let div1;
	let t10;
	let section1;
	let div2;
	let h62;
	let t11_value = /*content_2*/ ctx[3].tag + "";
	let t11;
	let t12;
	let h63;
	let t13_value = /*content_2*/ ctx[3].title + "";
	let t13;
	let t14;
	let p2;
	let t15_value = /*content_2*/ ctx[3].description + "";
	let t15;
	let t16;
	let div3;
	let t17;
	let section2;
	let div4;
	let h64;
	let t18_value = /*content_3*/ ctx[4].tag + "";
	let t18;
	let t19;
	let h65;
	let t20_value = /*content_3*/ ctx[4].title + "";
	let t20;
	let t21;
	let p3;
	let t22_value = /*content_3*/ ctx[4].description + "";
	let t22;
	let t23;
	let div5;
	let t24;
	let section3;
	let div6;
	let h66;
	let t25_value = /*content_4*/ ctx[5].tag + "";
	let t25;
	let t26;
	let h67;
	let t27_value = /*content_4*/ ctx[5].title + "";
	let t27;
	let t28;
	let p4;
	let t29_value = /*content_4*/ ctx[5].description + "";
	let t29;
	let t30;
	let div7;
	let t31;
	let section4;
	let div8;
	let h68;
	let t32_value = /*content_5*/ ctx[6].tag + "";
	let t32;
	let t33;
	let h69;
	let t34_value = /*content_5*/ ctx[6].title + "";
	let t34;
	let t35;
	let p5;
	let t36_value = /*content_5*/ ctx[6].description_1 + "";
	let t36;
	let t37;
	let p6;
	let t38_value = /*content_5*/ ctx[6].description_2 + "";
	let t38;
	let t39;
	let p7;
	let t40;
	let t41;
	let div9;
	let t42;
	let a;
	let t43_value = /*content_action*/ ctx[8].label + "";
	let t43;
	let a_href_value;

	return {
		c() {
			div13 = element("div");
			div12 = element("div");
			div11 = element("div");
			div10 = element("div");
			h3 = element("h3");
			t0 = text(/*content_title*/ ctx[0]);
			t1 = space();
			p0 = element("p");
			t2 = text(/*content_description*/ ctx[1]);
			t3 = space();
			section0 = element("section");
			div0 = element("div");
			h60 = element("h6");
			t4 = text(t4_value);
			t5 = space();
			h61 = element("h6");
			t6 = text(t6_value);
			t7 = space();
			p1 = element("p");
			t8 = text(t8_value);
			t9 = space();
			div1 = element("div");
			t10 = space();
			section1 = element("section");
			div2 = element("div");
			h62 = element("h6");
			t11 = text(t11_value);
			t12 = space();
			h63 = element("h6");
			t13 = text(t13_value);
			t14 = space();
			p2 = element("p");
			t15 = text(t15_value);
			t16 = space();
			div3 = element("div");
			t17 = space();
			section2 = element("section");
			div4 = element("div");
			h64 = element("h6");
			t18 = text(t18_value);
			t19 = space();
			h65 = element("h6");
			t20 = text(t20_value);
			t21 = space();
			p3 = element("p");
			t22 = text(t22_value);
			t23 = space();
			div5 = element("div");
			t24 = space();
			section3 = element("section");
			div6 = element("div");
			h66 = element("h6");
			t25 = text(t25_value);
			t26 = space();
			h67 = element("h6");
			t27 = text(t27_value);
			t28 = space();
			p4 = element("p");
			t29 = text(t29_value);
			t30 = space();
			div7 = element("div");
			t31 = space();
			section4 = element("section");
			div8 = element("div");
			h68 = element("h6");
			t32 = text(t32_value);
			t33 = space();
			h69 = element("h6");
			t34 = text(t34_value);
			t35 = space();
			p5 = element("p");
			t36 = text(t36_value);
			t37 = space();
			p6 = element("p");
			t38 = text(t38_value);
			t39 = space();
			p7 = element("p");
			t40 = text(/*note*/ ctx[7]);
			t41 = space();
			div9 = element("div");
			t42 = space();
			a = element("a");
			t43 = text(t43_value);
			this.h();
		},
		l(nodes) {
			div13 = claim_element(nodes, "DIV", { class: true, id: true });
			var div13_nodes = children(div13);
			div12 = claim_element(div13_nodes, "DIV", { class: true });
			var div12_nodes = children(div12);
			div11 = claim_element(div12_nodes, "DIV", { class: true });
			var div11_nodes = children(div11);
			div10 = claim_element(div11_nodes, "DIV", { class: true });
			var div10_nodes = children(div10);
			h3 = claim_element(div10_nodes, "H3", {});
			var h3_nodes = children(h3);
			t0 = claim_text(h3_nodes, /*content_title*/ ctx[0]);
			h3_nodes.forEach(detach);
			t1 = claim_space(div10_nodes);
			p0 = claim_element(div10_nodes, "P", { id: true, class: true });
			var p0_nodes = children(p0);
			t2 = claim_text(p0_nodes, /*content_description*/ ctx[1]);
			p0_nodes.forEach(detach);
			t3 = claim_space(div10_nodes);
			section0 = claim_element(div10_nodes, "SECTION", { id: true });
			var section0_nodes = children(section0);
			div0 = claim_element(section0_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h60 = claim_element(div0_nodes, "H6", { class: true });
			var h60_nodes = children(h60);
			t4 = claim_text(h60_nodes, t4_value);
			h60_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t5 = claim_space(section0_nodes);
			h61 = claim_element(section0_nodes, "H6", { class: true });
			var h61_nodes = children(h61);
			t6 = claim_text(h61_nodes, t6_value);
			h61_nodes.forEach(detach);
			t7 = claim_space(section0_nodes);
			p1 = claim_element(section0_nodes, "P", { class: true });
			var p1_nodes = children(p1);
			t8 = claim_text(p1_nodes, t8_value);
			p1_nodes.forEach(detach);
			t9 = claim_space(section0_nodes);
			div1 = claim_element(section0_nodes, "DIV", {});
			var div1_nodes = children(div1);
			div1_nodes.forEach(detach);
			section0_nodes.forEach(detach);
			t10 = claim_space(div10_nodes);
			section1 = claim_element(div10_nodes, "SECTION", { id: true });
			var section1_nodes = children(section1);
			div2 = claim_element(section1_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			h62 = claim_element(div2_nodes, "H6", { class: true });
			var h62_nodes = children(h62);
			t11 = claim_text(h62_nodes, t11_value);
			h62_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t12 = claim_space(section1_nodes);
			h63 = claim_element(section1_nodes, "H6", { class: true });
			var h63_nodes = children(h63);
			t13 = claim_text(h63_nodes, t13_value);
			h63_nodes.forEach(detach);
			t14 = claim_space(section1_nodes);
			p2 = claim_element(section1_nodes, "P", { class: true });
			var p2_nodes = children(p2);
			t15 = claim_text(p2_nodes, t15_value);
			p2_nodes.forEach(detach);
			t16 = claim_space(section1_nodes);
			div3 = claim_element(section1_nodes, "DIV", {});
			var div3_nodes = children(div3);
			div3_nodes.forEach(detach);
			section1_nodes.forEach(detach);
			t17 = claim_space(div10_nodes);
			section2 = claim_element(div10_nodes, "SECTION", { id: true });
			var section2_nodes = children(section2);
			div4 = claim_element(section2_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);
			h64 = claim_element(div4_nodes, "H6", { class: true });
			var h64_nodes = children(h64);
			t18 = claim_text(h64_nodes, t18_value);
			h64_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			t19 = claim_space(section2_nodes);
			h65 = claim_element(section2_nodes, "H6", { class: true });
			var h65_nodes = children(h65);
			t20 = claim_text(h65_nodes, t20_value);
			h65_nodes.forEach(detach);
			t21 = claim_space(section2_nodes);
			p3 = claim_element(section2_nodes, "P", { class: true });
			var p3_nodes = children(p3);
			t22 = claim_text(p3_nodes, t22_value);
			p3_nodes.forEach(detach);
			t23 = claim_space(section2_nodes);
			div5 = claim_element(section2_nodes, "DIV", {});
			var div5_nodes = children(div5);
			div5_nodes.forEach(detach);
			section2_nodes.forEach(detach);
			t24 = claim_space(div10_nodes);
			section3 = claim_element(div10_nodes, "SECTION", { id: true });
			var section3_nodes = children(section3);
			div6 = claim_element(section3_nodes, "DIV", { class: true });
			var div6_nodes = children(div6);
			h66 = claim_element(div6_nodes, "H6", { class: true });
			var h66_nodes = children(h66);
			t25 = claim_text(h66_nodes, t25_value);
			h66_nodes.forEach(detach);
			div6_nodes.forEach(detach);
			t26 = claim_space(section3_nodes);
			h67 = claim_element(section3_nodes, "H6", { class: true });
			var h67_nodes = children(h67);
			t27 = claim_text(h67_nodes, t27_value);
			h67_nodes.forEach(detach);
			t28 = claim_space(section3_nodes);
			p4 = claim_element(section3_nodes, "P", { class: true });
			var p4_nodes = children(p4);
			t29 = claim_text(p4_nodes, t29_value);
			p4_nodes.forEach(detach);
			t30 = claim_space(section3_nodes);
			div7 = claim_element(section3_nodes, "DIV", {});
			var div7_nodes = children(div7);
			div7_nodes.forEach(detach);
			section3_nodes.forEach(detach);
			t31 = claim_space(div10_nodes);
			section4 = claim_element(div10_nodes, "SECTION", { id: true });
			var section4_nodes = children(section4);
			div8 = claim_element(section4_nodes, "DIV", { class: true });
			var div8_nodes = children(div8);
			h68 = claim_element(div8_nodes, "H6", { class: true });
			var h68_nodes = children(h68);
			t32 = claim_text(h68_nodes, t32_value);
			h68_nodes.forEach(detach);
			div8_nodes.forEach(detach);
			t33 = claim_space(section4_nodes);
			h69 = claim_element(section4_nodes, "H6", { class: true });
			var h69_nodes = children(h69);
			t34 = claim_text(h69_nodes, t34_value);
			h69_nodes.forEach(detach);
			t35 = claim_space(section4_nodes);
			p5 = claim_element(section4_nodes, "P", { class: true });
			var p5_nodes = children(p5);
			t36 = claim_text(p5_nodes, t36_value);
			p5_nodes.forEach(detach);
			t37 = claim_space(section4_nodes);
			p6 = claim_element(section4_nodes, "P", { class: true });
			var p6_nodes = children(p6);
			t38 = claim_text(p6_nodes, t38_value);
			p6_nodes.forEach(detach);
			t39 = claim_space(section4_nodes);
			p7 = claim_element(section4_nodes, "P", { class: true });
			var p7_nodes = children(p7);
			t40 = claim_text(p7_nodes, /*note*/ ctx[7]);
			p7_nodes.forEach(detach);
			t41 = claim_space(section4_nodes);
			div9 = claim_element(section4_nodes, "DIV", {});
			var div9_nodes = children(div9);
			div9_nodes.forEach(detach);
			section4_nodes.forEach(detach);
			t42 = claim_space(div10_nodes);
			a = claim_element(div10_nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t43 = claim_text(a_nodes, t43_value);
			a_nodes.forEach(detach);
			div10_nodes.forEach(detach);
			div11_nodes.forEach(detach);
			div12_nodes.forEach(detach);
			div13_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(p0, "id", "content-paragraph-1");
			attr(p0, "class", "p-large svelte-1b6g14u");
			attr(h60, "class", "h700");
			attr(div0, "class", "tag-yellow-large svelte-1b6g14u");
			attr(h61, "class", "title h700 svelte-1b6g14u");
			attr(p1, "class", "p-large");
			attr(section0, "id", "1");
			attr(h62, "class", "h700");
			attr(div2, "class", "tag-yellow-large svelte-1b6g14u");
			attr(h63, "class", "title h700 svelte-1b6g14u");
			attr(p2, "class", "p-large");
			attr(section1, "id", "2");
			attr(h64, "class", "h700");
			attr(div4, "class", "tag-yellow-large svelte-1b6g14u");
			attr(h65, "class", "title h700 svelte-1b6g14u");
			attr(p3, "class", "p-large");
			attr(section2, "id", "3");
			attr(h66, "class", "h700");
			attr(div6, "class", "tag-yellow-large svelte-1b6g14u");
			attr(h67, "class", "title h700 svelte-1b6g14u");
			attr(p4, "class", "p-large");
			attr(section3, "id", "4");
			attr(h68, "class", "h700");
			attr(div8, "class", "tag-yellow-large svelte-1b6g14u");
			attr(h69, "class", "title h700 svelte-1b6g14u");
			attr(p5, "class", "multi-line p-large svelte-1b6g14u");
			attr(p6, "class", "p-large");
			attr(p7, "class", "p-large");
			attr(section4, "id", "5");
			attr(a, "class", "secondary-button svelte-1b6g14u");
			attr(a, "href", a_href_value = /*content_action*/ ctx[8].url);
			attr(div10, "class", "section-container content svelte-1b6g14u");
			attr(div11, "class", "wrapper svelte-1b6g14u");
			attr(div12, "class", "container svelte-1b6g14u");
			attr(div13, "class", "section");
			attr(div13, "id", "section-e3eacfa8");
		},
		m(target, anchor) {
			insert_hydration(target, div13, anchor);
			append_hydration(div13, div12);
			append_hydration(div12, div11);
			append_hydration(div11, div10);
			append_hydration(div10, h3);
			append_hydration(h3, t0);
			append_hydration(div10, t1);
			append_hydration(div10, p0);
			append_hydration(p0, t2);
			append_hydration(div10, t3);
			append_hydration(div10, section0);
			append_hydration(section0, div0);
			append_hydration(div0, h60);
			append_hydration(h60, t4);
			append_hydration(section0, t5);
			append_hydration(section0, h61);
			append_hydration(h61, t6);
			append_hydration(section0, t7);
			append_hydration(section0, p1);
			append_hydration(p1, t8);
			append_hydration(section0, t9);
			append_hydration(section0, div1);
			append_hydration(div10, t10);
			append_hydration(div10, section1);
			append_hydration(section1, div2);
			append_hydration(div2, h62);
			append_hydration(h62, t11);
			append_hydration(section1, t12);
			append_hydration(section1, h63);
			append_hydration(h63, t13);
			append_hydration(section1, t14);
			append_hydration(section1, p2);
			append_hydration(p2, t15);
			append_hydration(section1, t16);
			append_hydration(section1, div3);
			append_hydration(div10, t17);
			append_hydration(div10, section2);
			append_hydration(section2, div4);
			append_hydration(div4, h64);
			append_hydration(h64, t18);
			append_hydration(section2, t19);
			append_hydration(section2, h65);
			append_hydration(h65, t20);
			append_hydration(section2, t21);
			append_hydration(section2, p3);
			append_hydration(p3, t22);
			append_hydration(section2, t23);
			append_hydration(section2, div5);
			append_hydration(div10, t24);
			append_hydration(div10, section3);
			append_hydration(section3, div6);
			append_hydration(div6, h66);
			append_hydration(h66, t25);
			append_hydration(section3, t26);
			append_hydration(section3, h67);
			append_hydration(h67, t27);
			append_hydration(section3, t28);
			append_hydration(section3, p4);
			append_hydration(p4, t29);
			append_hydration(section3, t30);
			append_hydration(section3, div7);
			append_hydration(div10, t31);
			append_hydration(div10, section4);
			append_hydration(section4, div8);
			append_hydration(div8, h68);
			append_hydration(h68, t32);
			append_hydration(section4, t33);
			append_hydration(section4, h69);
			append_hydration(h69, t34);
			append_hydration(section4, t35);
			append_hydration(section4, p5);
			append_hydration(p5, t36);
			append_hydration(section4, t37);
			append_hydration(section4, p6);
			append_hydration(p6, t38);
			append_hydration(section4, t39);
			append_hydration(section4, p7);
			append_hydration(p7, t40);
			append_hydration(section4, t41);
			append_hydration(section4, div9);
			append_hydration(div10, t42);
			append_hydration(div10, a);
			append_hydration(a, t43);
		},
		p(ctx, [dirty]) {
			if (dirty & /*content_title*/ 1) set_data(t0, /*content_title*/ ctx[0]);
			if (dirty & /*content_description*/ 2) set_data(t2, /*content_description*/ ctx[1]);
			if (dirty & /*content_1*/ 4 && t4_value !== (t4_value = /*content_1*/ ctx[2].tag + "")) set_data(t4, t4_value);
			if (dirty & /*content_1*/ 4 && t6_value !== (t6_value = /*content_1*/ ctx[2].title + "")) set_data(t6, t6_value);
			if (dirty & /*content_1*/ 4 && t8_value !== (t8_value = /*content_1*/ ctx[2].description + "")) set_data(t8, t8_value);
			if (dirty & /*content_2*/ 8 && t11_value !== (t11_value = /*content_2*/ ctx[3].tag + "")) set_data(t11, t11_value);
			if (dirty & /*content_2*/ 8 && t13_value !== (t13_value = /*content_2*/ ctx[3].title + "")) set_data(t13, t13_value);
			if (dirty & /*content_2*/ 8 && t15_value !== (t15_value = /*content_2*/ ctx[3].description + "")) set_data(t15, t15_value);
			if (dirty & /*content_3*/ 16 && t18_value !== (t18_value = /*content_3*/ ctx[4].tag + "")) set_data(t18, t18_value);
			if (dirty & /*content_3*/ 16 && t20_value !== (t20_value = /*content_3*/ ctx[4].title + "")) set_data(t20, t20_value);
			if (dirty & /*content_3*/ 16 && t22_value !== (t22_value = /*content_3*/ ctx[4].description + "")) set_data(t22, t22_value);
			if (dirty & /*content_4*/ 32 && t25_value !== (t25_value = /*content_4*/ ctx[5].tag + "")) set_data(t25, t25_value);
			if (dirty & /*content_4*/ 32 && t27_value !== (t27_value = /*content_4*/ ctx[5].title + "")) set_data(t27, t27_value);
			if (dirty & /*content_4*/ 32 && t29_value !== (t29_value = /*content_4*/ ctx[5].description + "")) set_data(t29, t29_value);
			if (dirty & /*content_5*/ 64 && t32_value !== (t32_value = /*content_5*/ ctx[6].tag + "")) set_data(t32, t32_value);
			if (dirty & /*content_5*/ 64 && t34_value !== (t34_value = /*content_5*/ ctx[6].title + "")) set_data(t34, t34_value);
			if (dirty & /*content_5*/ 64 && t36_value !== (t36_value = /*content_5*/ ctx[6].description_1 + "")) set_data(t36, t36_value);
			if (dirty & /*content_5*/ 64 && t38_value !== (t38_value = /*content_5*/ ctx[6].description_2 + "")) set_data(t38, t38_value);
			if (dirty & /*note*/ 128) set_data(t40, /*note*/ ctx[7]);
			if (dirty & /*content_action*/ 256 && t43_value !== (t43_value = /*content_action*/ ctx[8].label + "")) set_data(t43, t43_value);

			if (dirty & /*content_action*/ 256 && a_href_value !== (a_href_value = /*content_action*/ ctx[8].url)) {
				attr(a, "href", a_href_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div13);
		}
	};
}

function instance$5($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { content_title } = $$props;
	let { content_description } = $$props;
	let { content_1 } = $$props;
	let { content_2 } = $$props;
	let { content_3 } = $$props;
	let { content_4 } = $$props;
	let { content_5 } = $$props;
	let { note } = $$props;
	let { content_action } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(9, favicon = $$props.favicon);
		if ('content_title' in $$props) $$invalidate(0, content_title = $$props.content_title);
		if ('content_description' in $$props) $$invalidate(1, content_description = $$props.content_description);
		if ('content_1' in $$props) $$invalidate(2, content_1 = $$props.content_1);
		if ('content_2' in $$props) $$invalidate(3, content_2 = $$props.content_2);
		if ('content_3' in $$props) $$invalidate(4, content_3 = $$props.content_3);
		if ('content_4' in $$props) $$invalidate(5, content_4 = $$props.content_4);
		if ('content_5' in $$props) $$invalidate(6, content_5 = $$props.content_5);
		if ('note' in $$props) $$invalidate(7, note = $$props.note);
		if ('content_action' in $$props) $$invalidate(8, content_action = $$props.content_action);
	};

	return [
		content_title,
		content_description,
		content_1,
		content_2,
		content_3,
		content_4,
		content_5,
		note,
		content_action,
		favicon
	];
}

class Component$5 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$5, create_fragment$5, safe_not_equal, {
			favicon: 9,
			content_title: 0,
			content_description: 1,
			content_1: 2,
			content_2: 3,
			content_3: 4,
			content_4: 5,
			content_5: 6,
			note: 7,
			content_action: 8
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i].link;
	return child_ctx;
}

// (70:4) {#each nav as { link }}
function create_each_block$1(ctx) {
	let h6;
	let a;
	let t0_value = /*link*/ ctx[3].label + "";
	let t0;
	let a_target_value;
	let a_href_value;
	let t1;

	return {
		c() {
			h6 = element("h6");
			a = element("a");
			t0 = text(t0_value);
			t1 = space();
			this.h();
		},
		l(nodes) {
			h6 = claim_element(nodes, "H6", { id: true, class: true });
			var h6_nodes = children(h6);
			a = claim_element(h6_nodes, "A", { target: true, class: true, href: true });
			var a_nodes = children(a);
			t0 = claim_text(a_nodes, t0_value);
			a_nodes.forEach(detach);
			t1 = claim_space(h6_nodes);
			h6_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "target", a_target_value = /*link*/ ctx[3].label.includes('Whitepaper')
			? '_blank'
			: '_self');

			attr(a, "class", "link svelte-14fdjq7");
			attr(a, "href", a_href_value = /*link*/ ctx[3].url);
			attr(h6, "id", "links");
			attr(h6, "class", "h950 svelte-14fdjq7");
		},
		m(target, anchor) {
			insert_hydration(target, h6, anchor);
			append_hydration(h6, a);
			append_hydration(a, t0);
			append_hydration(h6, t1);
		},
		p(ctx, dirty) {
			if (dirty & /*nav*/ 1 && t0_value !== (t0_value = /*link*/ ctx[3].label + "")) set_data(t0, t0_value);

			if (dirty & /*nav*/ 1 && a_target_value !== (a_target_value = /*link*/ ctx[3].label.includes('Whitepaper')
			? '_blank'
			: '_self')) {
				attr(a, "target", a_target_value);
			}

			if (dirty & /*nav*/ 1 && a_href_value !== (a_href_value = /*link*/ ctx[3].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(h6);
		}
	};
}

function create_fragment$6(ctx) {
	let div;
	let footer;
	let nav_1;
	let t0;
	let span;
	let p;
	let t1;
	let each_value = /*nav*/ ctx[0];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$1(get_each_context$1(ctx, each_value, i));
	}

	return {
		c() {
			div = element("div");
			footer = element("footer");
			nav_1 = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t0 = space();
			span = element("span");
			p = element("p");
			t1 = text(/*copyright*/ ctx[1]);
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true, id: true });
			var div_nodes = children(div);
			footer = claim_element(div_nodes, "FOOTER", { class: true });
			var footer_nodes = children(footer);
			nav_1 = claim_element(footer_nodes, "NAV", { class: true });
			var nav_1_nodes = children(nav_1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_1_nodes);
			}

			nav_1_nodes.forEach(detach);
			t0 = claim_space(footer_nodes);
			span = claim_element(footer_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			p = claim_element(span_nodes, "P", { id: true, class: true });
			var p_nodes = children(p);
			t1 = claim_text(p_nodes, /*copyright*/ ctx[1]);
			p_nodes.forEach(detach);
			span_nodes.forEach(detach);
			footer_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(nav_1, "class", "svelte-14fdjq7");
			attr(p, "id", "copyright");
			attr(p, "class", "p-small svelte-14fdjq7");
			attr(span, "class", "svelte-14fdjq7");
			attr(footer, "class", "section-container svelte-14fdjq7");
			attr(div, "class", "section");
			attr(div, "id", "section-e7721667");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, footer);
			append_hydration(footer, nav_1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav_1, null);
				}
			}

			append_hydration(footer, t0);
			append_hydration(footer, span);
			append_hydration(span, p);
			append_hydration(p, t1);
		},
		p(ctx, [dirty]) {
			if (dirty & /*nav*/ 1) {
				each_value = /*nav*/ ctx[0];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$1(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav_1, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}

			if (dirty & /*copyright*/ 2) set_data(t1, /*copyright*/ ctx[1]);
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$6($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { nav } = $$props;
	let { copyright } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(2, favicon = $$props.favicon);
		if ('nav' in $$props) $$invalidate(0, nav = $$props.nav);
		if ('copyright' in $$props) $$invalidate(1, copyright = $$props.copyright);
	};

	return [nav, copyright, favicon];
}

class Component$6 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$6, create_fragment$6, safe_not_equal, { favicon: 2, nav: 0, copyright: 1 });
	}
}

/* generated by Svelte v3.58.0 */

function instance$7($$self, $$props, $$invalidate) {
	let { favicon } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(0, favicon = $$props.favicon);
	};

	return [favicon];
}

class Component$7 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$7, null, safe_not_equal, { favicon: 0 });
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$7(ctx) {
	let component_0;
	let t0;
	let component_1;
	let t1;
	let component_2;
	let t2;
	let component_3;
	let t3;
	let component_4;
	let t4;
	let component_5;
	let t5;
	let component_6;
	let current;

	component_0 = new Component({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				}
			}
		});

	component_1 = new Component$2({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				logo: {
					"image": {
						"alt": "logo",
						"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686165013778unlok-logo2%20copy.svg",
						"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686165013778unlok-logo2%20copy.svg",
						"size": 3
					},
					"title": ""
				},
				site_nav: [
					{
						"link": { "url": "/personal", "label": "Personal" }
					},
					{
						"link": {
							"url": "/business",
							"label": "Business",
							"active": false
						}
					},
					{
						"link": { "url": "/investor", "label": "Investor" }
					}
				],
				site_nav_button: { "url": "/portal", "label": "Get Started" }
			}
		});

	component_2 = new Component$3({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				hero_title_1: "Staking at UNLOK:",
				hero_title_2: "Unlocking High Stakes and High Rewards",
				hero_action: { "url": "/", "label": "Whitepaper" },
				hero_image: {
					"alt": "Reward Tiers",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686607590000reward-tiers-app%20copy%202.svg",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686607590000reward-tiers-app%20copy%202.svg",
					"size": 43
				}
			}
		});

	component_3 = new Component$4({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				content_title: "Empowering Autonomy and Flexibility",
				content_description: "At UNLOK, we believe in empowering our users with flexibility, autonomy, and rewarding opportunities through our staking mechanism. Staking UNLOK tokens allow you to earn passive rewards and give you complete control over your staking preferences.",
				content_tag_1: "Choose Your Staking Preferences",
				content_paragraph_1: "With UNLOK's staking feature, users have the freedom to choose the exact amount they want to stake and the duration of the staking period. By participating in staking, you can earn reflective rewards through token reflections. We've designed our platform with user convenience in mind, offering full interoperability and a streamlined UI.",
				content_tag_2: "Seamless Integration with Your Wallet",
				content_paragraph_2: "Through the UNLOK dashboard application, users can easily connect their wallets and access the embedded staking feature. This allows for a seamless and hassle-free staking experience directly within your wallet. Reflective rewards are calculated on a 24-hour basis and credited to your wallet at the end of each cycle.",
				content_tag_3: "Unlock Higher Yields with Fixed-Term Staking",
				content_paragraph_3: "For those seeking higher yields in exchange for longer staking periods, UNLOK offers a fixed-term staking feature. This enables users to lock their tokens for specific durations, such as 30 days, 3 months, 6 months, or 1 year, and receive proportional percentage yields at the end of the staking period. What's more, fixed staking comes with an added bonus that is exclusive to this staking option.",
				content_tag_4: "Unlock Higher Tiers, Greater Rewards",
				content_paragraph_4: "UNLOK rewards its loyal users through a tiered system, where different levels of held or staked tokens unlock access to exceptional yields and rewards. As you increase the number of tokens held or staked, you gain entry into higher tiers, enjoying even greater benefits and earning potential.",
				content_tag_5: "Unlock High Stakes and High Rewards",
				content_paragraph_5: "With UNLOK's staking feature, users have the freedom to choose the exact amount they want to stake and the duration of the staking period. By participating in staking, you can earn reflective rewards through token reflections. We've designed our platform with user convenience in mind, offering full interoperability and a streamlined UI."
			}
		});

	component_4 = new Component$5({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				content_title: "UNLOK Tokenomics: Powering the Future of Blockchain Rewards",
				content_description: "Our carefully designed token allocation ensures the seamless functioning and growth of the UNLOK ecosystem. Here's a breakdown of how UNLOK tokens will be distributed:",
				content_1: {
					"tag": "Unallocated Reserve: Flexibility and Adaptability ",
					"title": "9.25% - 700 MILLION tokens",
					"description": "With UNLOK's staking feature, users have the freedom to choose the exact amount they want to stake and the duration of the staking period. By participating in staking, you can earn reflective rewards through token reflections. We've designed our platform with user convenience in mind, offering full interoperability and a streamlined UI."
				},
				content_2: {
					"tag": "Primer Token: Empowering Merchants",
					"title": "5% - 175 MILLION tokens",
					"description": "Primer tokens will be held in a multi-sig wallet and made immediately claimable. These tokens will be manually distributed to eligible merchants, fostering their active participation and engagement."
				},
				content_3: {
					"tag": "Founding Team: Recognizing Dedication",
					"title": "4% - 437.5 MILLION tokens",
					"description": "A portion of the token supply is allocated to compensate our dedicated executive team for their invaluable contributions to building and advancing the UNLOK ecosystem."
				},
				content_4: {
					"tag": "Marketing: Creating Impactful Brand Awareness",
					"title": "3.75% - 131.25 MILLION tokens",
					"description": "To reach a wider audience and create impactful brand awareness, a percentage of tokens is dedicated to supporting our comprehensive marketing efforts. This includes online and out-of-home advertising, strategic influencer partnerships, press releases, and engaging content writing services."
				},
				content_5: {
					"tag": "Employee Salaries: Valuing Our In-House Team",
					"title": "3% - 306.25 MILLION tokens",
					"description_1": "We value our in-house team members' hard work and dedication, who strive to make UNLOK an exceptional ecosystem. This token allocation rewards our talented employees for their continuous efforts. ",
					"description_2": "By meticulously allocating UNLOK tokens, we ensure our blockchain rewards platform's sustainability, innovation, and long-term success. As we continue to grow and evolve, our tokenomics will adapt to meet the needs of our vibrant community."
				},
				note: "*Note: The percentages and token amounts mentioned are for illustrative purposes and are subject to change based on the final token distribution plan.",
				content_action: { "url": "/", "label": "Whitepaper" }
			}
		});

	component_5 = new Component$6({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				nav: [
					{
						"link": {
							"url": "/tokenomics",
							"label": "Tokenomics"
						}
					},
					{
						"link": {
							"url": "/privacy",
							"label": "Privacy Policy"
						}
					},
					{
						"link": {
							"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/Whitepaper.pdf?t=2023-06-23T23%3A35%3A42.985Z",
							"label": "Whitepaper"
						}
					},
					{
						"link": {
							"url": "https://unlokloyalty.com#contact-us",
							"label": "Contact Us"
						}
					}
				],
				copyright: "© 2023 UNLOK. All rights reserved."
			}
		});

	component_6 = new Component$7({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				}
			}
		});

	return {
		c() {
			create_component(component_0.$$.fragment);
			t0 = space();
			create_component(component_1.$$.fragment);
			t1 = space();
			create_component(component_2.$$.fragment);
			t2 = space();
			create_component(component_3.$$.fragment);
			t3 = space();
			create_component(component_4.$$.fragment);
			t4 = space();
			create_component(component_5.$$.fragment);
			t5 = space();
			create_component(component_6.$$.fragment);
		},
		l(nodes) {
			claim_component(component_0.$$.fragment, nodes);
			t0 = claim_space(nodes);
			claim_component(component_1.$$.fragment, nodes);
			t1 = claim_space(nodes);
			claim_component(component_2.$$.fragment, nodes);
			t2 = claim_space(nodes);
			claim_component(component_3.$$.fragment, nodes);
			t3 = claim_space(nodes);
			claim_component(component_4.$$.fragment, nodes);
			t4 = claim_space(nodes);
			claim_component(component_5.$$.fragment, nodes);
			t5 = claim_space(nodes);
			claim_component(component_6.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(component_0, target, anchor);
			insert_hydration(target, t0, anchor);
			mount_component(component_1, target, anchor);
			insert_hydration(target, t1, anchor);
			mount_component(component_2, target, anchor);
			insert_hydration(target, t2, anchor);
			mount_component(component_3, target, anchor);
			insert_hydration(target, t3, anchor);
			mount_component(component_4, target, anchor);
			insert_hydration(target, t4, anchor);
			mount_component(component_5, target, anchor);
			insert_hydration(target, t5, anchor);
			mount_component(component_6, target, anchor);
			current = true;
		},
		p: noop,
		i(local) {
			if (current) return;
			transition_in(component_0.$$.fragment, local);
			transition_in(component_1.$$.fragment, local);
			transition_in(component_2.$$.fragment, local);
			transition_in(component_3.$$.fragment, local);
			transition_in(component_4.$$.fragment, local);
			transition_in(component_5.$$.fragment, local);
			transition_in(component_6.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(component_0.$$.fragment, local);
			transition_out(component_1.$$.fragment, local);
			transition_out(component_2.$$.fragment, local);
			transition_out(component_3.$$.fragment, local);
			transition_out(component_4.$$.fragment, local);
			transition_out(component_5.$$.fragment, local);
			transition_out(component_6.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(component_0, detaching);
			if (detaching) detach(t0);
			destroy_component(component_1, detaching);
			if (detaching) detach(t1);
			destroy_component(component_2, detaching);
			if (detaching) detach(t2);
			destroy_component(component_3, detaching);
			if (detaching) detach(t3);
			destroy_component(component_4, detaching);
			if (detaching) detach(t4);
			destroy_component(component_5, detaching);
			if (detaching) detach(t5);
			destroy_component(component_6, detaching);
		}
	};
}

class Component$8 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$7, safe_not_equal, {});
	}
}

export default Component$8;
