-- ===== Key System (must pass before the script runs) =====
local function __y2k_keygate()
-- ============================================================================
--  Y2k key provider  (drop-in replacement for the Junkie SDK)
--  Talks to YOUR Cloudflare Worker + KV key server (server-side hashing, HWID
--  auto-bind, expiry). CONFIGURE the two URLs below. Server: server-example/.
-- ============================================================================
local Junkie = {}
do
	local KEY_API  = "https://y2k-keys.y2kscript.workers.dev"  -- your deployed Worker (LIVE)
	local KEY_LINK = "https://work.ink/2Dgt/ks-int12887-kq76mlra7lo" -- work.ink key link

	local HttpService = game:GetService("HttpService")
	local function enc(s) local ok, r = pcall(function() return HttpService:UrlEncode(s) end) return ok and r or s end
	local function httpGet(u)
		for _, f in ipairs({
			function() return game:HttpGetAsync(u) end,
			function() return game:HttpGet(u) end,
			function() return request and request({ Url = u, Method = "GET" }).Body end,
		}) do
			local ok, b = pcall(f); if ok and type(b) == "string" then return b end
		end
		return nil
	end
	local function hwid()
		local id
		pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
		if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
		return tostring(id or "unknown")
	end

	function Junkie.get_key_link() return KEY_LINK end
	function Junkie.check_key(key)
		if not key or key == "" then return { valid = false, message = "No key entered" } end
		local hw = hwid()
		local url = KEY_API .. "/check?key=" .. enc(key) .. "&hwid=" .. enc(hw) .. "&t=" .. tostring(os.time())
		local body = httpGet(url)
		if not body then return { valid = false, message = "Key server unreachable" } end
		local b = string.lower(body)
		if string.find(b, "ok", 1, true) then
			getgenv().HWID = hw
			return { valid = true, message = "KEY_VALID", hwid = hw }
		elseif string.find(b, "expired", 1, true) then
			return { valid = false, message = "Key expired" }
		elseif string.find(b, "hwid", 1, true) then
			return { valid = false, message = "Key locked to another device" }
		else
			return { valid = false, message = "Invalid key" }
		end
	end
end


local TweenService = game:GetService("TweenService")
local UserInputService = game:GetService("UserInputService")
local RunService = game:GetService("RunService")
local Players = game:GetService("Players")
local Lighting = game:GetService("Lighting")
local HttpService = game:GetService("HttpService")

local Icons = {
	Shield = "rbxassetid://105619007041452",
	Loading = "rbxassetid://116535712789945",
	Lock = "rbxassetid://114355063515473",
	Key = "rbxassetid://93569468678423",
	Check = "rbxassetid://119783053916823",
	CheckCircle = "rbxassetid://10709790644",
	XCircle = "rbxassetid://10747384394",
	Warning = "rbxassetid://130226573962640",
	Globe = "rbxassetid://10734950309",
	Info = "rbxassetid://94529541997278",
	ExternalLink = "rbxassetid://71038734318580",
	Copy = "rbxassetid://107485544510830",
	Spinner = "rbxassetid://10709767827",
	Database = "rbxassetid://114209748010261",
	Sparkles = "rbxassetid://10709767827",
	ErrorFolder = "rbxassetid://113312905787220",
	Candy = "rbxassetid://10709767827",
	JunkieNewIcon = "rbxassetid://75038032192167"
}

local function hasFileSystemSupport()
    local hasWritefile = pcall(function() return type(writefile) == "function" end)
    local hasReadfile = pcall(function() return type(readfile) == "function" end)
    local hasIsfile = pcall(function() return type(isfile) == "function" end)
    return hasWritefile and hasReadfile and hasIsfile
end

local fileSystemSupported = hasFileSystemSupport()

local function saveVerifiedKey(key)
    if not fileSystemSupported then return false end
    local ok = pcall(function()
        writefile("verified_key.txt", key)
    end)
    return ok
end

local function loadVerifiedKey()
    if not fileSystemSupported then 
        return nil 
    end
    
    local ok, content = pcall(function()
        return readfile("verified_key.txt")
    end)
    
    if not ok or not content then 
        return nil 
    end
    return content
end

local function clearSavedKey()
    if not fileSystemSupported then return false end
    local ok = pcall(function() delfile("verified_key.txt") end)
    return ok
end

local Configuration = {
	ScreenGuiName = "JunkieKeySystem",
	Window = {Size = UDim2.new(0, 333, 0, 500)},
	Colors = {
		Bg = Color3.fromRGB(12, 12, 12),
		Primary = Color3.fromRGB(59, 130, 246),
		PrimaryDark = Color3.fromRGB(37, 99, 235),
		StatusIdle = Color3.fromRGB(249, 115, 22),
		StatusSuccess = Color3.fromRGB(16, 185, 129),
		StatusError = Color3.fromRGB(239, 68, 68),
		StatusVerifying = Color3.fromRGB(59, 130, 246),
		StatusWarning = Color3.fromRGB(254, 188, 46),
		TextMain = Color3.fromRGB(255, 255, 255),
		TextSec = Color3.fromRGB(161, 161, 170),
		TextMuted = Color3.fromRGB(113, 113, 122),
		Border = Color3.fromRGB(255, 255, 255),
		TrafficRed = Color3.fromRGB(255, 95, 87),
		TrafficYellow = Color3.fromRGB(254, 188, 46),
		TrafficGreen = Color3.fromRGB(40, 200, 64),
		Success = Color3.fromRGB(50, 205, 110),
		Error = Color3.fromRGB(245, 70, 90),
		Warning = Color3.fromRGB(255, 200, 50)
	},
	BorderTransparency = 0.15,
	Animations = {
		VeryFast = 0.1,
		Fast = 0.2,
		Medium = 0.4,
		Slow = 0.5,
		VerySlow = 0.6,
		Bounce = 0.6
	},
	Fonts = {
		Title = 24,
		Subtitle = 12,
		Button = 14,
		Input = 16,
		Body = 13,
		Small = 11,
		Tiny = 12
	}
}

local Utils = {}

Utils.Tween = function(obj, props, time, style, dir)
	local t =
		TweenService:Create(
		obj,
		TweenInfo.new(time or 0.3, style or Enum.EasingStyle.Quint, dir or Enum.EasingDirection.Out),
		props
	)
	t:Play()
	return t
end

Utils.CreateCorner = function(parent, radius)
	local corner = Instance.new("UICorner")
	corner.CornerRadius = UDim.new(0, radius or Configuration.CornerRadius)
	corner.Parent = parent
	return corner
end

Utils.Round = function(obj, radius)
	local c = Instance.new("UICorner")
	c.CornerRadius = UDim.new(0, radius or 12)
	c.Parent = obj
	return c
end

Utils.TweenBack = function(instance, properties, duration)
	return Utils.Tween(instance, properties, duration, Enum.EasingStyle.Back, Enum.EasingDirection.Out)
end

Utils.CreateStroke = function(parent, color, thickness, transparency)
	local stroke = Instance.new("UIStroke")
	stroke.Color = color or Configuration.Colors.Border
	stroke.Thickness = thickness or 1
	stroke.Transparency = transparency or 0.77
	stroke.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	stroke.Parent = parent
	return stroke
end

Utils.Stroke = function(obj, color, thick, trans)
	local s = Instance.new("UIStroke")
	s.Color = color or Color3.new(1, 1, 1)
	s.Thickness = thick or 1
	s.Transparency = trans or 0.9
	s.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	s.Parent = obj
	return s
end

Utils.CreateGradient = function(parent, color1, color2, rotation)
	local gradient = Instance.new("UIGradient")
	gradient.Color =
		ColorSequence.new(
		{
			ColorSequenceKeypoint.new(0, color1),
			ColorSequenceKeypoint.new(1, color2)
		}
	)
	gradient.Rotation = rotation or 300
	gradient.Parent = parent
	return gradient
end

local function SetBlur(enabled)
	local blur = Lighting:FindFirstChild("JunkieBlur")
	if enabled then
		if not blur then
			blur = Instance.new("BlurEffect")
			blur.Name = "JunkieBlur"
			blur.Size = 0
			blur.Parent = Lighting
		end
		Utils.Tween(blur, {Size = 24}, Configuration.Animations.Bounce)
	elseif blur then
		Utils.Tween(blur, {Size = 0}, Configuration.Animations.Medium)
		task.delay(
			0.4,
			function()
				blur:Destroy()
			end
		)
	end
end

local ToastSystem = {ActiveToasts = {}, MaxToasts = 3, ToastSpacing = 10}

ToastSystem.Create = function(parent, message, toastType, duration, statusCode)
	local colors = {
		success = Configuration.Colors.Success,
		error = Configuration.Colors.Error,
		warning = Configuration.Colors.Warning,
		info = Configuration.Colors.Primary
	}
	local icons = {
		success = Icons.CheckCircle,
		error = Icons.ErrorFolder,
		warning = Icons.Warning,
		info = Icons.Info
	}
	local toastColor = colors[toastType] or colors.Bg
	local toastIcon = icons[toastType] or nil
	if #ToastSystem.ActiveToasts >= ToastSystem.MaxToasts then
		local oldest = table.remove(ToastSystem.ActiveToasts, 1)
		if oldest and oldest.Parent then
			oldest:Destroy()
		end
	end
	local toastHeight = 56
	local toast = Instance.new("Frame")
	toast.Name = tick()
	toast.Size = UDim2.new(0, 0, 0, toastHeight)
	toast.Position = UDim2.new(0.5, 0, 0, 20)
	toast.AnchorPoint = Vector2.new(0.5, 0)
	toast.BackgroundColor3 = Configuration.Colors.Bg
	toast.BackgroundTransparency = 0.5
	toast.BorderSizePixel = 0
	toast.ZIndex = 300
	toast.ClipsDescendants = true
	toast.Parent = parent
	Utils.Round(toast, 14)
	Utils.CreateStroke(toast, toastColor, 1, 0.1)
	Utils.CreateGradient(toast, Configuration.Colors.Bg, Configuration.Colors.Bg, 1)
	local iconBg = Instance.new("Frame")
	iconBg.Name = "IconBg"
	iconBg.Size = UDim2.new(0, 36, 0, 36)
	iconBg.Position = UDim2.new(0, 12, 0.5, 0)
	iconBg.AnchorPoint = Vector2.new(0, 0.5)
	iconBg.BackgroundColor3 = toastColor
	iconBg.BackgroundTransparency = 0.85
	iconBg.BorderSizePixel = 0
	iconBg.ZIndex = 301
	iconBg.Parent = toast
	Utils.Round(iconBg, 18)
	local icon = Instance.new("ImageLabel")
	icon.Name = "Icon"
	icon.Size = UDim2.new(0, 20, 0, 20)
	icon.Position = UDim2.new(0.5, 0, 0.5, 0)
	icon.AnchorPoint = Vector2.new(0.5, 0.5)
	icon.BackgroundTransparency = 1
	icon.Image = toastIcon
	icon.ImageColor3 = toastColor
	icon.ZIndex = 302
	icon.Parent = iconBg
	local textContainer = Instance.new("Frame")
	textContainer.Name = "TextContainer"
	textContainer.Size = UDim2.new(1, statusCode and -110 or -60, 1, 0)
	textContainer.Position = UDim2.new(0, 56, 0, 0)
	textContainer.BackgroundTransparency = 1
	textContainer.ZIndex = 301
	textContainer.Parent = toast
	local text = Instance.new("TextLabel")
	text.Name = "Message"
	text.Size = UDim2.new(1, 0, 1, 0)
	text.BackgroundTransparency = 1
	text.Text = message or ""
	text.TextColor3 = Configuration.Colors.TextMain
	text.TextSize = Configuration.Fonts.Body
	text.Font = Enum.Font.GothamMedium
	text.TextXAlignment = Enum.TextXAlignment.Left
	text.TextYAlignment = Enum.TextYAlignment.Center
	text.TextWrapped = true
	text.ZIndex = 301
	text.Parent = textContainer
	if statusCode then
		local statusBadge = Instance.new("Frame")
		statusBadge.Name = "StatusBadge"
		statusBadge.Size = UDim2.new(0, 44, 0, 28)
		statusBadge.Position = UDim2.new(1, -12, 0.5, 0)
		statusBadge.AnchorPoint = Vector2.new(1, 0.5)
		statusBadge.BackgroundColor3 = toastColor
		statusBadge.BackgroundTransparency = 0.8
		statusBadge.BorderSizePixel = 0
		statusBadge.ZIndex = 301
		statusBadge.Parent = toast
		Utils.Round(statusBadge, 8)
		Utils.CreateStroke(statusBadge, toastColor, 1, Configuration.BorderTransparency)
		local statusCodeLabel = Instance.new("TextLabel")
		statusCodeLabel.Name = "StatusCode"
		statusCodeLabel.Size = UDim2.new(1, 0, 1, 0)
		statusCodeLabel.BackgroundTransparency = 1
		statusCodeLabel.Text = tostring(statusCode)
		statusCodeLabel.TextColor3 = toastColor
		statusCodeLabel.TextSize = Configuration.Fonts.Small
		statusCodeLabel.Font = Enum.Font.GothamBold
		statusCodeLabel.ZIndex = 302
		statusCodeLabel.Parent = statusBadge
	end
	table.insert(ToastSystem.ActiveToasts, toast)
	ToastSystem.RepositionToasts()
	local targetWidth = 320
	Utils.TweenBack(toast, {Size = UDim2.new(0, targetWidth, 0, toastHeight)}, Configuration.Animations.Medium)
	task.delay(
		duration or 3.5,
		function()
			if toast.Parent then
				Utils.Tween(
					toast,
					{
						Position = UDim2.new(0.5, 0, 0, -80),
						BackgroundTransparency = 1
					},
					Configuration.Animations.Medium
				)
				for i, t in ipairs(ToastSystem.ActiveToasts) do
					if t == toast then
						table.remove(ToastSystem.ActiveToasts, i)
						break
					end
				end
				task.wait(Configuration.Animations.Medium)
				toast:Destroy()
				ToastSystem.RepositionToasts()
			end
		end
	)
	return toast
end

ToastSystem.RepositionToasts = function()
	for i, toast in ipairs(ToastSystem.ActiveToasts) do
		local targetY = 20 + ((i - 1) * (60 + ToastSystem.ToastSpacing))
		Utils.Tween(toast, {Position = UDim2.new(0.5, 0, 0, targetY)}, Configuration.Animations.Medium)
	end
end

local function Build()
	local parent = game:GetService("CoreGui")
	local old = parent:FindFirstChild(Configuration.ScreenGuiName)
	if old then
		old:Destroy()
	end
	local screen = Instance.new("ScreenGui")
	screen.Name = Configuration.ScreenGuiName
	screen.ResetOnSpawn = false
	screen.Parent = parent

	-- Discord banner (top of screen, transparent, blinking + glow)
	local discordBanner = Instance.new("TextLabel")
	discordBanner.Name = "DiscordBanner"
	discordBanner.Size = UDim2.new(0, 400, 0, 32)
	discordBanner.Position = UDim2.new(0.5, 0, 0, 10)
	discordBanner.AnchorPoint = Vector2.new(0.5, 0)
	discordBanner.BackgroundTransparency = 1
	discordBanner.Text = "Join https://discord.gg/EFFKrfFkPQ"
	discordBanner.TextColor3 = Color3.fromRGB(88, 101, 242)
	discordBanner.TextSize = 16
	discordBanner.Font = Enum.Font.GothamBold
	discordBanner.TextTransparency = 0
	discordBanner.Parent = screen

	local bannerStroke = Instance.new("UIStroke")
	bannerStroke.Color = Color3.fromRGB(88, 101, 242)
	bannerStroke.Thickness = 2
	bannerStroke.Transparency = 0.3
	bannerStroke.Parent = discordBanner

	task.spawn(function()
		while discordBanner and discordBanner.Parent do
			Utils.Tween(discordBanner, {TextTransparency = 0.4}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.7}, 0.6)
			task.wait(0.6)
			Utils.Tween(discordBanner, {TextTransparency = 0}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.3}, 0.6)
			task.wait(0.6)
		end
	end)

	local overlay = Instance.new("Frame")
	overlay.Size = UDim2.fromScale(1, 1)
	overlay.BackgroundColor3 = Color3.new(0, 0, 0)
	overlay.BackgroundTransparency = 1
	overlay.Parent = screen
	Utils.Tween(overlay, {BackgroundTransparency = 1}, 1)
	SetBlur(true)
	local main = Instance.new("Frame")
	main.Size = Configuration.Window.Size
	main.Position = UDim2.new(0.5, 0, 0.5, 60)
	main.AnchorPoint = Vector2.new(0.5, 0.5)
	main.BackgroundColor3 = Configuration.Colors.Bg
	main.BackgroundTransparency = 0.2
	main.ClipsDescendants = true
	main.Parent = screen
	Utils.Round(main, 24)
	Utils.Stroke(main, Color3.new(1, 1, 1), 1, 0.92)
	local glass = Instance.new("Frame")
	glass.Size = UDim2.fromScale(1, 1)
	glass.BackgroundColor3 = Color3.new(1, 1, 1)
	glass.BackgroundTransparency = 0.985
	glass.ZIndex = 0
	glass.Parent = main
	Utils.Round(glass, 24)
	local bar = Instance.new("Frame")
	bar.Size = UDim2.new(1, 0, 0, 54)
	bar.BackgroundTransparency = 1
	bar.Parent = main
	local dots = Instance.new("Frame")
	dots.Size = UDim2.new(0, 54, 0, 12)
	dots.Position = UDim2.new(0, 20, 0.5, 0)
	dots.AnchorPoint = Vector2.new(0, 0.5)
	dots.BackgroundTransparency = 1
	dots.Parent = bar
	local dColors = {
		Configuration.Colors.TrafficRed,
		Configuration.Colors.TrafficYellow,
		Configuration.Colors.TrafficGreen
	}
	for i, c in ipairs(dColors) do
		local d = Instance.new("Frame")
		d.Size = UDim2.fromOffset(12, 12)
		d.Position = UDim2.fromOffset((i - 1) * 18, 0)
		d.BackgroundColor3 = c
		d.BorderSizePixel = 0
		d.Parent = dots
		Utils.Round(d, 6)
	end
	local titleText = Instance.new("TextLabel")
	titleText.Size = UDim2.new(1, 0, 1, 0)
	titleText.Text = "JUNKIE"
	titleText.TextColor3 = Color3.new(1, 1, 1)
	titleText.TextTransparency = 0.7
	titleText.TextSize = 10
	titleText.Font = Enum.Font.GothamBold
	titleText.BackgroundTransparency = 1
	titleText.Parent = bar
	local content = Instance.new("ScrollingFrame")
	content.Size = UDim2.new(1, 0, 1, -54)
	content.Position = UDim2.new(0, 0, 0, 54)
	content.BackgroundTransparency = 1
	content.ScrollBarThickness = 0
	content.CanvasSize = UDim2.new(0, 0, 0, 440)
	content.Parent = main
	local list = Instance.new("UIListLayout")
	list.Padding = UDim.new(0, 24)
	list.HorizontalAlignment = Enum.HorizontalAlignment.Center
	list.Parent = content
	local pad = Instance.new("UIPadding")
	pad.PaddingTop = UDim.new(0, 5)
	pad.Parent = content
	local logoContainer = Instance.new("Frame")
	logoContainer.Size = UDim2.fromOffset(80, 80)
	logoContainer.BackgroundColor3 = Configuration.Colors.Primary
	logoContainer.Parent = content
	Utils.Round(logoContainer, 20)
	local grad = Instance.new("UIGradient")
	grad.Color = ColorSequence.new(Configuration.Colors.Primary, Configuration.Colors.PrimaryDark)
	grad.Rotation = 45
	grad.Parent = logoContainer
	local sIcon = Instance.new("ImageLabel")
	sIcon.Size = UDim2.fromScale(1, 1)
	sIcon.Position = UDim2.fromScale(0.5, 0.5)
	sIcon.AnchorPoint = Vector2.new(0.5, 0.5)
	sIcon.Image = Icons.JunkieNewIcon
	sIcon.ScaleType = Enum.ScaleType.Fit
	sIcon.BackgroundTransparency = 1
	sIcon.Parent = logoContainer
	local titleArea = Instance.new("Frame")
	titleArea.Size = UDim2.new(1, 0, 0, 44)
	titleArea.BackgroundTransparency = 1
	titleArea.Parent = content
	local mainTitle = Instance.new("TextLabel")
	mainTitle.Size = UDim2.new(1, 0, 0, 26)
	mainTitle.Text = "Junkie"
	mainTitle.TextColor3 = Color3.new(1, 1, 1)
	mainTitle.TextSize = 26
	mainTitle.Font = Enum.Font.GothamBold
	mainTitle.BackgroundTransparency = 1
	mainTitle.Parent = titleArea
	local subTitle = Instance.new("TextLabel")
	subTitle.Size = UDim2.new(1, 0, 0, 16)
	subTitle.Position = UDim2.fromOffset(0, 28)
	subTitle.Text = "junkie-development.de"
	subTitle.TextColor3 = Configuration.Colors.TextSec
	subTitle.TextSize = 13
	subTitle.Font = Enum.Font.Gotham
	subTitle.BackgroundTransparency = 1
	subTitle.Parent = titleArea
	local statusCard = Instance.new("Frame")
	statusCard.Size = UDim2.new(0, 280, 0, 68)
	statusCard.BackgroundColor3 = Color3.new(1, 1, 1)
	statusCard.BackgroundTransparency = 0.96
	statusCard.Parent = content
	Utils.Round(statusCard, 16)
	local sStroke = Utils.Stroke(statusCard, Color3.new(1, 1, 1), 1, 0.95)
	local sIconBg = Instance.new("Frame")
	sIconBg.Size = UDim2.fromOffset(42, 42)
	sIconBg.Position = UDim2.new(0, 14, 0.5, 0)
	sIconBg.AnchorPoint = Vector2.new(0, 0.5)
	sIconBg.BackgroundColor3 = Configuration.Colors.StatusIdle
	sIconBg.BackgroundTransparency = 0.9
	sIconBg.Parent = statusCard
	Utils.Round(sIconBg, 21)
	local sImg = Instance.new("ImageLabel")
	sImg.Size = UDim2.fromScale(0.5, 0.5)
	sImg.Position = UDim2.fromScale(0.5, 0.5)
	sImg.AnchorPoint = Vector2.new(0.5, 0.5)
	sImg.Image = Icons.Lock
	sImg.ImageColor3 = Configuration.Colors.StatusIdle
	sImg.BackgroundTransparency = 1
	sImg.Parent = sIconBg
	local sLabel = Instance.new("TextLabel")
	sLabel.Size = UDim2.new(1, -70, 0, 14)
	sLabel.Position = UDim2.fromOffset(70, 16)
	sLabel.Text = "CURRENT STATUS"
	sLabel.TextColor3 = Configuration.Colors.TextMuted
	sLabel.TextSize = 10
	sLabel.Font = Enum.Font.GothamBold
	sLabel.TextXAlignment = Enum.TextXAlignment.Left
	sLabel.BackgroundTransparency = 1
	sLabel.Parent = statusCard
	local sValue = Instance.new("TextLabel")
	sValue.Size = UDim2.new(1, -70, 0, 20)
	sValue.Position = UDim2.fromOffset(70, 32)
	sValue.Text = "No key detected"
	sValue.TextColor3 = Configuration.Colors.StatusIdle
	sValue.TextSize = 15
	sValue.Font = Enum.Font.GothamMedium
	sValue.TextXAlignment = Enum.TextXAlignment.Left
	sValue.BackgroundTransparency = 1
	sValue.Parent = statusCard
	local inputFrame = Instance.new("Frame")
	inputFrame.Size = UDim2.new(0, 280, 0, 52)
	inputFrame.BackgroundColor3 = Color3.new(1, 1, 1)
	inputFrame.BackgroundTransparency = 0.975
	inputFrame.Parent = content
	Utils.Round(inputFrame, 14)
	local iStroke = Utils.Stroke(inputFrame, Color3.new(1, 1, 1), 1, 0.95)
	local kIcon = Instance.new("ImageLabel")
	kIcon.Size = UDim2.fromOffset(18, 18)
	kIcon.Position = UDim2.new(0, 14, 0.5, 0)
	kIcon.AnchorPoint = Vector2.new(0, 0.5)
	kIcon.Image = Icons.Key
	kIcon.ImageColor3 = Configuration.Colors.TextMuted
	kIcon.BackgroundTransparency = 1
	kIcon.Parent = inputFrame
	local box = Instance.new("TextBox")
	box.Size = UDim2.new(1, -85, 1, 0)
	box.Position = UDim2.fromOffset(45, 0)
	box.Text = ""
	box.PlaceholderText = "Enter your key..."
	box.TextColor3 = Color3.new(1, 1, 1)
	box.TextSize = 14
	box.Font = Enum.Font.Gotham
	box.BackgroundTransparency = 1
	box.TextXAlignment = Enum.TextXAlignment.Left
	box.Parent = inputFrame
	local paste = Instance.new("ImageButton")
	paste.Size = UDim2.fromOffset(18, 18)
	paste.Position = UDim2.new(1, -14, 0.5, 0)
	paste.AnchorPoint = Vector2.new(1, 0.5)
	paste.Image = Icons.Copy
	paste.ImageColor3 = Configuration.Colors.TextMuted
	paste.BackgroundTransparency = 1
	paste.Parent = inputFrame
	local btnRow = Instance.new("Frame")
	btnRow.Size = UDim2.new(0, 280, 0, 50)
	btnRow.BackgroundTransparency = 1
	btnRow.Parent = content
	local redeem = Instance.new("TextButton")
	redeem.Size = UDim2.new(0.5, -8, 1, 0)
	redeem.BackgroundColor3 = Configuration.Colors.Primary
	redeem.Text = "Redeem"
	redeem.TextColor3 = Color3.new(1, 1, 1)
	redeem.Font = Enum.Font.GothamBold
	redeem.TextSize = 14
	redeem.AutoButtonColor = false
	redeem.Parent = btnRow
	Utils.Round(redeem, 14)
	local getKey = Instance.new("TextButton")
	getKey.Size = UDim2.new(0.5, -8, 1, 0)
	getKey.Position = UDim2.new(0.5, 8, 0, 0)
	getKey.BackgroundColor3 = Color3.new(1, 1, 1)
	getKey.BackgroundTransparency = 0.955
	getKey.Text = "Get Key"
	getKey.TextColor3 = Color3.new(1, 1, 1)
	getKey.Font = Enum.Font.GothamBold
	getKey.TextSize = 14
	getKey.AutoButtonColor = false
	getKey.Parent = btnRow
	Utils.Round(getKey, 14)
	Utils.Stroke(getKey, Color3.new(1, 1, 1), 1, 0.94)
	local function ApplyHover(btn)
		local baseColor = btn.BackgroundColor3
		btn.MouseEnter:Connect(
			function()
				Utils.Tween(
					btn,
					{
						BackgroundColor3 = baseColor:Lerp(Color3.new(1, 1, 1), 0.1)
					},
					0.2
				)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset + 4, btn.Size.Y.Scale, btn.Size.Y.Offset + 2)
					},
					0.2
				)
			end
		)
		btn.MouseLeave:Connect(
			function()
				Utils.Tween(btn, {BackgroundColor3 = baseColor}, 0.2)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset - 4, btn.Size.Y.Scale, btn.Size.Y.Offset - 2)
					},
					0.2
				)
			end
		)
	end
	ApplyHover(redeem)
	ApplyHover(getKey)
	box.Focused:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.5, Thickness = 1.2}, 0.3)
		end
	)
	box.FocusLost:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.95, Thickness = 1}, 0.3)
		end
	)
	local spinConnection
	local dotsThread
	local function SetStatus(state)
		if spinConnection then
			spinConnection:Disconnect()
			spinConnection = nil
			sImg.Rotation = 0
		end
		if dotsThread then
			task.cancel(dotsThread)
			dotsThread = nil
		end
		local color = Configuration.Colors.StatusIdle
		local icon = Icons.Lock
		local text = "No key detected"
		if state == "verifying" then
			color = Configuration.Colors.StatusVerifying
			icon = Icons.Loading
			text = "Verifying access"
			spinConnection =
				RunService.Heartbeat:Connect(
				function(dt)
					if not sImg or not sImg.Parent then
						if spinConnection then
							spinConnection:Disconnect()
						end
						spinConnection = nil
						return
					end
					sImg.Rotation = (sImg.Rotation + dt * 360) % 360
				end
			)
			local dots = {".", "..", "...", ""}
			local i = 1
			dotsThread =
				task.spawn(
				function()
					while sValue and sValue.Parent do
						if not sValue.Text:find("Verifying access", 1, true) then
							break
						end
						sValue.Text = text .. dots[i]
						i = (i % #dots) + 1
						task.wait(0.45)
					end
				end
			)
		elseif state == "success" then
			color = Configuration.Colors.StatusSuccess
			icon = Icons.CheckCircle
			text = "Access Granted"
		elseif state == "error" then
			color = Configuration.Colors.StatusError
			icon = Icons.XCircle
			text = "Invalid Key"
		end
		Utils.Tween(sValue, {TextColor3 = color}, 0.35)
		Utils.Tween(sImg, {ImageColor3 = color}, 0.35)
		Utils.Tween(sIconBg, {BackgroundColor3 = color}, 0.35)
		sValue.Text = text
		sImg.Image = icon
	end
	redeem.MouseButton1Click:Connect(
		function()
			local key = box.Text:upper()
			SetStatus("verifying")
			redeem.Text = "..."
			redeem.Active = false
            local result = Junkie.check_key(key)
			redeem.Active = true
			redeem.Text = "Redeem"
			if not result then
				SetStatus("error")
				ToastSystem.Create(screen, "API request failed: " .. tostring(result), "error")
				return
			end
			if result.valid then
                saveVerifiedKey(key)
                getgenv().SCRIPT_KEY = key
                SetStatus("success")
                ToastSystem.Create(screen, "Access granted!", "success", nil, status)
                task.wait(0.8)
                SetBlur(false)
                Utils.Tween(
                    main,
                    {
                        Position = UDim2.new(0.5, 0, 0.5, 100),
                        BackgroundTransparency = 1
                    },
                    0.7,
                    Enum.EasingStyle.Exponential,
                    Enum.EasingDirection.In
                )
                task.delay(
                    0.7,
                    function()
                        screen:Destroy()
                    end
                )
			else
				SetStatus("error")
				ToastSystem.Create(screen, result.message or "Invalid key", "error", nil, status)
			end
		end
	)
	getKey.MouseButton1Click:Connect(
		function()
			setclipboard(Junkie.get_key_link())
			ToastSystem.Create(screen, "Key link has been copied to clipboard", "success")
		end
	)
	paste.MouseButton1Click:Connect(
		function()
			ToastSystem.Create(screen, "Paste functionality not supported in Roblox (security reasons)", "warning")
		end
	)
	main.Position = UDim2.new(0.5, 0, 0.5, 100)
	main.BackgroundTransparency = 1
	Utils.Tween(
		main,
		{
			Position = UDim2.new(0.5, 0, 0.5, 0),
			BackgroundTransparency = 0.2
		},
		1,
		Enum.EasingStyle.Exponential
	)
	local dragging, dragStart, startPos
	bar.InputBegan:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = true
				dragStart = input.Position
				startPos = main.Position
			end
		end
	)
	UserInputService.InputChanged:Connect(
		function(input)
			if dragging and input.UserInputType == Enum.UserInputType.MouseMovement then
				local delta = input.Position - dragStart
				main.Position =
					UDim2.new(startPos.X.Scale, startPos.X.Offset + delta.X, startPos.Y.Scale, startPos.Y.Offset + delta.Y)
			end
		end
	)
	UserInputService.InputEnded:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = false
			end
		end
	)
	return screen
end

local savedKey = loadVerifiedKey()
local keyToCheck = savedKey
if not keyToCheck then
    keyToCheck = getgenv().SCRIPT_KEY
end

local result = Junkie.check_key(keyToCheck)
if result and result.valid then
    if result.message == "KEYLESS" then
        getgenv().SCRIPT_KEY = "KEYLESS"
    elseif result.message == "KEY_VALID" then
        if not savedKey and keyToCheck then
            saveVerifiedKey(keyToCheck)
        end
        getgenv().SCRIPT_KEY = keyToCheck
    else
        Build()
    end
else
    Build()
end

while not getgenv().SCRIPT_KEY do
    task.wait(0.1)
end
end
__y2k_keygate()
-- ===== Protected payload =====
-- Protected with Vm runtime. Tampering halts execution.
-- Vm protection runtime (bundled). Do not edit by hand.
local Crypt = (function()
--!nonstrict
-- ============================================================================
--  Crypt.lua  --  lightweight obfuscation / integrity primitives
--  Part of the Vm protection runtime. No external deps. Luau-safe.
--
--  Provides: XOR string cipher, FNV-1a hash, base64, and a small PRNG so the
--  runtime can hide embedded strings (URLs, function names) and verify
--  integrity without leaving plaintext secrets in the bytecode.
-- ============================================================================

local Crypt = {}

local schar, sbyte, ssub, srep = string.char, string.byte, string.sub, string.rep
local tconcat = table.concat
local bxor = bit32 and bit32.bxor or function(a, b)
	local r, p = 0, 1
	while a > 0 or b > 0 do
		local x, y = a % 2, b % 2
		if x ~= y then r = r + p end
		a, b, p = (a - x) / 2, (b - y) / 2, p * 2
	end
	return r
end

-- 32-bit multiply mod 2^32 that stays within double precision (2^53).
-- Splitting the accumulator into hi/lo 16-bit halves keeps every intermediate
-- product under 2^42, so no precision is lost (a plain h*16777619 overflows 2^53).
local function mul32(a, b)
	local ah = (a - a % 65536) / 65536   -- floor(a / 2^16), < 2^16
	local al = a % 65536                  -- a mod 2^16, < 2^16
	return ((ah * b % 65536) * 65536 + al * b) % 4294967296
end

-- FNV-1a 32-bit hash of a string (used for integrity fingerprints)
function Crypt.hash(s)
	local h = 2166136261
	for i = 1, #s do
		h = bxor(h, sbyte(s, i))
		h = mul32(h, 16777619)
	end
	return h
end

-- repeating-key XOR cipher (symmetric). key is a string.
function Crypt.xor(data, key)
	local out, kl = {}, #key
	for i = 1, #data do
		out[i] = schar(bxor(sbyte(data, i), sbyte(key, (i - 1) % kl + 1)))
	end
	return tconcat(out)
end

-- deterministic PRNG (xorshift) seeded from a string; for shuffling/jitter
function Crypt.rng(seed)
	local state = (type(seed) == "string") and Crypt.hash(seed) or (seed or 0x1234567)
	if state == 0 then state = 0x9E3779B9 end
	return function()
		state = bxor(state, (state * 32) % 4294967296)
		state = bxor(state, math.floor(state / 8))
		state = bxor(state, (state * 16384) % 4294967296)
		state = state % 4294967296
		return state / 4294967296
	end
end

-- base64 (so ciphertext survives as a string literal in the bundle)
local B64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
function Crypt.b64encode(data)
	local out = {}
	for i = 1, #data, 3 do
		local a, b, c = sbyte(data, i), sbyte(data, i + 1), sbyte(data, i + 2)
		local n = a * 65536 + (b or 0) * 256 + (c or 0)
		local c1 = math.floor(n / 262144) % 64
		local c2 = math.floor(n / 4096) % 64
		local c3 = math.floor(n / 64) % 64
		local c4 = n % 64
		out[#out + 1] = ssub(B64, c1 + 1, c1 + 1)
		out[#out + 1] = ssub(B64, c2 + 1, c2 + 1)
		out[#out + 1] = b and ssub(B64, c3 + 1, c3 + 1) or "="
		out[#out + 1] = c and ssub(B64, c4 + 1, c4 + 1) or "="
	end
	return tconcat(out)
end

local B64I
function Crypt.b64decode(data)
	if not B64I then
		B64I = {}
		for i = 1, #B64 do B64I[ssub(B64, i, i)] = i - 1 end
	end
	data = string.gsub(data, "[^" .. B64 .. "]", "")
	local out = {}
	for i = 1, #data, 4 do
		local a = B64I[ssub(data, i, i)] or 0
		local b = B64I[ssub(data, i + 1, i + 1)] or 0
		local c = B64I[ssub(data, i + 2, i + 2)]
		local d = B64I[ssub(data, i + 3, i + 3)]
		local n = a * 262144 + b * 4096 + (c or 0) * 64 + (d or 0)
		out[#out + 1] = schar(math.floor(n / 65536) % 256)
		if c then out[#out + 1] = schar(math.floor(n / 256) % 256) end
		if d then out[#out + 1] = schar(n % 256) end
	end
	return tconcat(out)
end

-- convenience: encrypt a plaintext to a portable token (b64(xor(data,key)))
function Crypt.seal(plaintext, key)
	return Crypt.b64encode(Crypt.xor(plaintext, key))
end
function Crypt.open(token, key)
	return Crypt.xor(Crypt.b64decode(token), key)
end

return Crypt

end)()
local Secure = (function()
--!nonstrict
-- ============================================================================
--  Secure.lua  --  capture real executor functions & expose protected proxies
--
--  THE CORE PROTECTION. At load time (before any spy can install hooks) we grab
--  references to the real executor functions into PRIVATE upvalues, then hand
--  the wrapped script only thin proxies. Because the proxies call the captured
--  originals directly, a spy that later hooks the GLOBAL `request` / `http` /
--  `readfile` never sees the script's calls -- they bypass the global.
--
--  Proxies are wrapped with newcclosure so they read as native C-closures:
--  iscclosure() passes, and getupvalues() is blocked on them by most executors,
--  hiding the captured originals from getgc/upvalue inspection.
-- ============================================================================

local Secure = {}

-- resolve the real global table as early as possible
local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local rawget, rawset = rawget, rawset
local iscc = iscclosure
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction or function(f) return f end

-- list of sensitive globals we proxy. (function-valued globals only)
local CAPTURE = {
	"request", "http_request", "readfile", "writefile", "appendfile", "isfile",
	"isfolder", "listfiles", "makefolder", "delfile", "delfolder", "loadstring",
	"getgenv", "getrawmetatable", "setrawmetatable", "hookfunction", "hookmetamethod",
	"newcclosure", "getnamecallmethod", "setclipboard", "queue_on_teleport",
	"getcustomasset", "fireclickdetector", "firetouchinterest", "fireproximityprompt",
	"isexecutorclosure", "checkcaller", "getconnections", "getcallingscript",
}

-- Capture the real functions. Returns a PRIVATE table (kept as an upvalue by the
-- caller -- never store this in a global).
function Secure.capture()
	local raw = {}

	-- http via the common executor spellings, in priority order
	raw.http = (syn and syn.request) or (http and http.request) or http_request or request
	-- guard: if http appears already hooked (became an l-closure), remember it
	raw.http_tampered = (iscc and raw.http and not iscc(raw.http)) or false

	for _, name in ipairs(CAPTURE) do
		local fn = rawget(realG, name)
		if type(fn) == "function" then
			-- clone where supported so even a later identity-swap of the global
			-- can't reach our reference
			local ok, c = pcall(clonef, fn)
			raw[name] = ok and c or fn
			raw[name .. "_genuine"] = (iscc and iscc(fn)) or false
		end
	end

	-- HttpGet/HttpGetAsync live on `game`; capture bound callers
	local okGame = pcall(function() return game and game.HttpGet end)
	if okGame and game then
		raw.HttpGet = function(url, ...) return game:HttpGet(url, ...) end
		raw.HttpGetAsync = function(url, ...) return game:HttpGetAsync(url, ...) end
	end

	return raw
end

-- Build the proxy table the sandbox exposes. `raw` is the private capture.
-- Each proxy is a newcclosure so its upvalues (the real fn) are not inspectable.
function Secure.proxies(raw)
	local P = {}

	local function wrap(realFn)
		if type(realFn) ~= "function" then return nil end
		return newcc(function(...) return realFn(...) end)
	end

	-- generic passthrough proxies
	for _, name in ipairs(CAPTURE) do
		if raw[name] then P[name] = wrap(raw[name]) end
	end

	-- unified HTTP proxy (the prime spy target). Accepts the standard {Url=...}.
	if raw.http then
		local http = raw.http
		P.request = newcc(function(opts) return http(opts) end)
		P.http_request = P.request
		if syn then P.syn = { request = P.request } end
	end
	if raw.HttpGet then
		P.HttpGet = newcc(function(url, ...) return raw.HttpGet(url, ...) end)
		P.HttpGetAsync = newcc(function(url, ...) return raw.HttpGetAsync(url, ...) end)
	end

	return P
end

-- Snapshot identities so Integrity can detect later replacement of our proxies.
function Secure.fingerprint(P)
	local fp = {}
	for k, v in pairs(P) do
		if type(v) == "function" then fp[k] = v end
	end
	return fp
end

return Secure

end)()
local Environment = (function()
--!nonstrict
-- ============================================================================
--  Environment.lua  --  the sealed sandbox the wrapped script runs inside
--
--  Builds a custom _ENV whose:
--    * function-valued executor globals resolve to PROTECTED PROXIES
--    * everything else falls through to the real globals (so game, workspace,
--      Instance, math, string, task, etc. all work -- full Luau semantics)
--    * writes stay local to the sandbox (script can't pollute real _G)
--    * the metatable is private (Integrity verifies it wasn't swapped)
--
--  This is the isolation layer: the script believes it has a normal global
--  environment, but its sensitive calls are routed through the Vm.
-- ============================================================================

local Environment = {}

function Environment.build(proxies, realG)
	realG = realG or (getgenv and getgenv()) or _G

	-- the sandbox's own storage for globals the script defines
	local store = {}

	-- private metatable (kept out of the sandbox; Integrity holds a ref)
	local mt = {}

	mt.__index = function(_, key)
		-- 1. protected proxy?
		local p = proxies[key]
		if p ~= nil then return p end
		-- 2. script-local global?
		local s = store[key]
		if s ~= nil then return s end
		-- 3. fall through to the real environment
		return realG[key]
	end

	mt.__newindex = function(_, key, value)
		-- keep all writes inside the sandbox (never touch real globals)
		store[key] = value
	end

	-- unique private lock token. __metatable makes getmetatable(env) return THIS
	-- (hiding the real mt) and makes setmetatable(env, ...) error -- so the env's
	-- metatable cannot be swapped. Integrity verifies this token is still in place.
	local lock = {}
	mt.__metatable = lock

	local env = setmetatable({}, mt)

	-- expose a sandboxed getfenv/getgenv so the script's own introspection
	-- returns the sandbox, not the real globals (don't leak the boundary)
	store.getgenv = function() return env end
	store._G = env
	store.shared = store.shared or {}

	return env, mt, store, lock
end

return Environment

end)()
local Integrity = (function()
--!nonstrict
-- ============================================================================
--  Integrity.lua  --  anti-tamper / anti-penetration
--
--  Verifies the runtime hasn't been hooked or swapped, both at startup and via
--  a background watchdog. On tamper it triggers a caller-supplied onTamper
--  (the Vm wipes the sandbox + halts).
--
--  Checks:
--   * capture genuineness   -- were the executor funcs already hooked at capture?
--   * proxy identity         -- have our proxies been replaced since fingerprint?
--   * env seal               -- is the sandbox __index/__newindex intact?
--   * hostile introspection  -- is something actively decompiling/hooking us?
--   * source checksum        -- does the protected payload still match?
-- ============================================================================

local Integrity = {}

local iscc = iscclosure
local getus = getupvalues or (debug and debug.getupvalues)

-- 1. Were any captured executor functions already hooks (l-closures) at capture?
function Integrity.checkCapture(raw)
	local suspicious = {}
	if raw.http_tampered then suspicious[#suspicious + 1] = "http" end
	for k, v in pairs(raw) do
		if string.sub(k, -8) == "_genuine" and v == false then
			suspicious[#suspicious + 1] = string.sub(k, 1, -9)
		end
	end
	return suspicious
end

-- 2. Our proxies must still be the exact functions we created.
function Integrity.checkProxies(P, fingerprint)
	for k, original in pairs(fingerprint) do
		if P[k] ~= original then return false, k end
	end
	return true
end

-- 3. The sandbox env metatable must be intact (not re-pointed to leak globals).
function Integrity.checkEnv(env, expectedMT)
	local mt = getmetatable(env)
	if mt ~= expectedMT then return false, "metatable" end
	return true
end

-- 4. Best-effort: detect if our own proxies have become inspectable (a sign a
--    de-hook tool unwrapped the cclosure). On a healthy executor getupvalues on
--    a newcclosure should be empty/blocked; non-empty => someone unwrapped it.
function Integrity.checkOpaque(P)
	if not getus then return true end
	for _, v in pairs(P) do
		if type(v) == "function" then
			local ok, ups = pcall(getus, v)
			if ok and type(ups) == "table" and next(ups) ~= nil then
				return false
			end
		end
	end
	return true
end

-- run all startup checks; returns ok, reason
function Integrity.startup(ctx)
	local sus = Integrity.checkCapture(ctx.raw)
	if #sus > 0 and ctx.strict then
		return false, "capture-hooked:" .. table.concat(sus, ",")
	end
	local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
	if not okP then return false, "proxy-swapped:" .. tostring(badKey) end
	local okE, why = Integrity.checkEnv(ctx.env, ctx.envLock)
	if not okE then return false, "env-" .. tostring(why) end
	if not Integrity.checkOpaque(ctx.proxies) then return false, "opaque-broken" end
	return true
end

-- background watchdog: re-run cheap checks on an interval and self-destruct.
-- Spawns through the Memory scope (ctx.mem) so the thread is tracked and
-- cancelled on cleanup -- it can never leak past the script's lifetime.
function Integrity.watchdog(ctx, onTamper)
	local wait_ = (task and task.wait) or wait
	local body = function()
		while ctx.alive do
			wait_(ctx.interval or 2)
			if not ctx.alive then return end
			local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
			local okE = Integrity.checkEnv(ctx.env, ctx.envLock)
			if not okP or not okE then
				ctx.alive = false
				pcall(onTamper, okP and "env" or ("proxy:" .. tostring(badKey)))
				return
			end
		end
	end
	if ctx.mem and ctx.mem.spawn then
		ctx.mem:spawn(body)
	else
		local spawn = (task and task.spawn) or spawn
		if spawn then spawn(body) end
	end
end

return Integrity

end)()
local Stealth = (function()
--!nonstrict
-- ============================================================================
--  Stealth.lua  --  comprehensive environment spoofing / anti-detection
--
--  Covers the full sUNC executor surface (docs.sunc.su). For each function an
--  anti-cheat could use to fingerprint the executor, detect hooks, or scan for
--  injected objects, we install a fake that answers "clean" -- while leaving the
--  function usable for everyone else.
--
--  Technique: hookfunction (rewrites the function OBJECT, so even a reference
--  the AC captured early is affected), replacement wrapped in newcclosure (stays
--  a C-closure -> passes iscclosure). Everything pcall-guarded; only spoofs what
--  the executor actually exposes.
--
--  HONEST: beats ACs that read these globals at runtime and trust them. Does NOT
--  beat an AC that ran fully before you, re-implements checks in its own VM, or
--  validates server-side. Raises the bar across games.
-- ============================================================================

local Stealth = {}

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction
local hookf = hookfunction
local cloneref_ = cloneref or function(x) return x end
local rawget, rawset = rawget, rawset

-- private registries (weak so we never pin objects alive)
local hiddenObjs = setmetatable({}, { __mode = "k" })  -- hide from gc/instance scans
local genuineFns = setmetatable({}, { __mode = "k" })  -- report as un-hooked / ours
local ourScripts = setmetatable({}, { __mode = "k" })  -- hide script bytecode/closure
local installed  = false

function Stealth.hide(o)        if o ~= nil then hiddenObjs[o] = true end return o end
function Stealth.markGenuine(f) if type(f) == "function" then genuineFns[f] = true end return f end
function Stealth.hideScript(s)  if s ~= nil then ourScripts[s] = true end return s end

-- ---- hook helpers ---------------------------------------------------------
-- CRITICAL: after hookfunction(real, repl), the `real` OBJECT behaves like repl.
-- So the replacement must NOT call `real` on its passthrough path (that would be
-- infinite recursion -> C stack overflow). We clone the original FIRST and have
-- the replacement call the unhooked clone. If we can't clone, we fall back to a
-- plain global swap (which leaves `real` itself untouched, so calling it is safe).
local function emplace(container, name, build)
	if type(container) ~= "table" then return end
	local real = rawget(container, name)
	if type(real) ~= "function" then return end
	if hookf and clonef then
		local okc, orig = pcall(clonef, real)
		if okc and type(orig) == "function" then
			local repl = newcc(build(orig))         -- repl -> clone (unhooked): safe
			genuineFns[repl] = true; hiddenObjs[repl] = true
			if pcall(hookf, real, repl) then return end
		end
	end
	-- fallback: global/table swap, repl -> real (real is NOT hooked here): safe
	local repl = newcc(build(real))
	genuineFns[repl] = true; hiddenObjs[repl] = true
	pcall(rawset, container, name, repl)
end

local function spoof(name, build)            emplace(realG, name, build) end
local function spoofIn(tbl, name, build)     emplace(tbl, name, build) end

-- filter our hidden/genuine objects out of an array-like result table.
local function filterArray(t)
	if type(t) ~= "table" then return t end
	local out = {}
	for i = 1, #t do
		local v = t[i]
		if not (hiddenObjs[v] or genuineFns[v]) then out[#out + 1] = v end
	end
	return out
end

-- ===========================================================================
function Stealth.install(opts)
	if installed then return end
	installed = true
	opts = opts or {}
	local fakeName = opts.spoofName            -- nil => "no executor"
	local fakeVer  = opts.spoofVersion or "1.0.0"

	-- DISGUISE: a real game LocalScript (cloneref'd) to report as the "calling
	-- script", so introspection sees a legit script instead of getcallingscript()
	-- == nil (which screams "injected"). On by default; opts.disguise=false to skip.
	local decoyScript = nil
	if opts.disguise ~= false then
		pcall(function()
			local lp = game:GetService("Players").LocalPlayer
			local char = lp and lp.Character
			decoyScript = (char and char:FindFirstChild("Animate"))
				or (lp and lp:FindFirstChildWhichIsA("LocalScript", true))
		end)
		if decoyScript then pcall(function() decoyScript = cloneref_(decoyScript) end) end
	end

	-- 1) IDENTITY ----------------------------------------------------------
	for _, n in ipairs({ "identifyexecutor", "getexecutorname", "iexecutor" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end

	-- 2) CLOSURE CHECKS ----------------------------------------------------
	spoof("iscclosure",       function(r) return function(f) if genuineFns[f] then return true  end return r(f) end end)
	spoof("isexecutorclosure",function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("isourclosure",     function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("islclosure",       function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("checkcaller",      function(r) return function() return false end end)
	-- stable fake hash for our funcs so repeated checks stay consistent
	spoof("getfunctionhash",  function(r) return function(f) if genuineFns[f] then return "00000000000000000000000000000000" end return r(f) end end)

	-- 3) ENVIRONMENT / GC scans -- strip our objects ----------------------
	spoof("getgc",     function(r) return function(...) return filterArray(r(...)) end end)
	spoof("filtergc",  function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	spoof("getreg",    function(r) return function(...) return filterArray(r(...)) end end)
	-- getgenv/getrenv must keep identity (callers rely on it); objects already hidden via getgc

	-- 4) INSTANCE scans -- strip our injected instances -------------------
	spoof("getinstances",    function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getnilinstances", function(r) return function(...) return filterArray(r(...)) end end)

	-- 5) SCRIPT scans -- hide our scripts/closures ------------------------
	spoof("getloadedmodules", function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getrunningscripts",function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getscripts",       function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getcallingscript", function(r) return function(...) local s = r(...); if ourScripts[s] or s == nil then return decoyScript end return s end end)
	spoof("getscriptbytecode",function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscriptclosure", function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscripthash",    function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	spoof("getsenv",          function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- 6) DEBUG introspection -- blank out for OUR functions ---------------
	if debug then
		spoofIn(debug, "getupvalue",  function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getupvalues", function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getconstant", function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getconstants",function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getproto",    function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getprotos",   function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
	end
	-- top-level mirrors (some executors expose these globally too)
	for _, n in ipairs({ "getupvalue","getupvalues","getconstant","getconstants","getproto","getprotos" }) do
		spoof(n, function(r) return function(f, ...)
			if genuineFns[f] then
				if string.sub(n, -1) == "s" then return {} end
				return nil
			end
			return r(f, ...)
		end end)
	end

	-- 7) common executor extras (Volt/Synapse/etc. spellings that may exist) ----
	for _, n in ipairs({ "getexecutorname", "getexecutor", "getexecutorinfo" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end
	-- decompiler-style probes: refuse on our scripts
	for _, n in ipairs({ "decompile", "disassemble", "dumpstring" }) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	end

	-- 7b) Potassium / extended closure + thread + hook checks --------------
	-- the big one: isfunctionhooked must say NO for the funcs your cheat hooks
	spoof("isfunctionhooked", function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isnewcclosure",    function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isourclosure",     function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	-- "is this the executor / a hook thread" -> no
	spoof("isourthread",      function(r) return function() return false end end)
	-- thread/script linkage: don't reveal our scripts
	spoof("getscriptfromthread", function(r) return function(t, ...) local s = r(t, ...) if ourScripts[s] then return nil end return s end end)
	spoof("getscriptthread",     function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("gettenv",             function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- Potassium oth.* (original-thread hooking) table
	local oth = rawget(realG, "oth")
	if type(oth) == "table" then
		spoofIn(oth, "is_hook_thread", function(r) return function() return false end end)
	end

	-- debug.* extras present on Potassium
	if debug then
		spoofIn(debug, "getcallstack", function(r) return function(...) return r(...) end end)  -- seam: frames aren't our objects
		-- getregistry: return a filtered COPY with our objects removed (AC scans are read-only)
		spoofIn(debug, "getregistry", function(r) return function(...)
			local reg = r(...)
			if type(reg) ~= "table" then return reg end
			local out = {}
			for k, v in pairs(reg) do
				if not (hiddenObjs[k] or hiddenObjs[v] or genuineFns[k] or genuineFns[v]) then
					out[k] = v
				end
			end
			return out
		end end)
		spoofIn(debug, "getinfo", function(r) return function(...) return r(...) end end)  -- seam
	end

	-- metatable seams: only safe to touch CONDITIONALLY. We do NOT blanket-fake
	-- getrawmetatable/getnamecallmethod -- faking the real game metatable breaks
	-- everything. If YOUR cheat hooks __namecall, register the clean function via
	-- Stealth.markGenuine(yourHook) and add a targeted getrawmetatable spoof.

	-- 8) USER-SUPPLIED EXTENSIONS (add Volt-specific names without editing code) -
	--    opts.identity   = { "voltname", ... }     -> spoofed like identifyexecutor
	--    opts.gcFilters  = { "somelist", ... }     -> array results have our objs removed
	--    opts.genuine    = { "iscustom", ... }     -> return clean for our funcs
	--    opts.scriptHide = { "getbytecode2", ... } -> return nothing for our scripts
	for _, n in ipairs(opts.identity or {}) do
		spoof(n, function() return function() if fakeName then return fakeName, fakeVer end return nil end end)
	end
	for _, n in ipairs(opts.gcFilters or {}) do
		spoof(n, function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	end
	for _, n in ipairs(opts.genuine or {}) do
		spoof(n, function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	end
	for _, n in ipairs(opts.scriptHide or {}) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	end

	return true
end

return Stealth

end)()
local Memory = (function()
--!nonstrict
-- ============================================================================
--  Memory.lua  --  resource scope + leak/overflow protection
--
--  Every thread, connection and disposable the VM creates is registered in a
--  scope. When the script ends (return, error, or tamper) the scope is torn down
--  deterministically: threads cancelled, connections disconnected, tables
--  cleared, GC forced. Plus a budget guard that collects GC the moment memory
--  crosses a threshold, so a runaway/hostile script can't balloon the VM.
--
--  Design notes:
--   * Registries that hold game objects use WEAK keys so they never pin memory.
--   * The scope holds STRONG refs to threads/connections (so it can cancel them)
--     but cleanup is GUARANTEED to run, bounding their lifetime.
--   * Counters are capped; nothing grows unbounded.
-- ============================================================================

local Memory = {}
Memory.__index = Memory

local taskLib   = task
local taskSpawn = (taskLib and taskLib.spawn) or spawn
local taskWait  = (taskLib and taskLib.wait) or wait
local taskDefer = (taskLib and taskLib.defer) or taskSpawn
local taskCancel = taskLib and taskLib.cancel
local cg = collectgarbage

local MAX_TRACKED = 4096   -- hard cap so the bookkeeping itself can't leak

function Memory.new()
	return setmetatable({
		alive = true,
		threads = {},
		conns = {},
		disposers = {},
		count = 0,
	}, Memory)
end

local function bounded(self)
	return self.count < MAX_TRACKED
end

-- spawn a tracked thread (auto-cancelled on cleanup)
function Memory:spawn(fn)
	if not self.alive or not bounded(self) then return end
	local co = taskSpawn(fn)
	self.threads[#self.threads + 1] = co
	self.count = self.count + 1
	return co
end

-- track an arbitrary resource with a disposer
function Memory:track(obj, dispose)
	if not self.alive or not bounded(self) then return obj end
	if dispose then
		self.disposers[#self.disposers + 1] = dispose
		self.count = self.count + 1
	end
	return obj
end

-- track a signal connection (auto-disconnected on cleanup)
function Memory:connect(signal, fn)
	if not self.alive or not bounded(self) then return end
	local ok, c = pcall(function() return signal:Connect(fn) end)
	if ok and c then
		self.conns[#self.conns + 1] = c
		self.count = self.count + 1
		return c
	end
end

-- deterministic teardown -- safe to call multiple times
function Memory:cleanup()
	if not self.alive then return end
	self.alive = false
	for _, c in ipairs(self.conns) do
		pcall(function() if c.Disconnect then c:Disconnect() elseif c.disconnect then c:disconnect() end end)
	end
	if taskCancel then
		for _, co in ipairs(self.threads) do pcall(taskCancel, co) end
	end
	for _, d in ipairs(self.disposers) do pcall(d) end
	self.conns, self.threads, self.disposers, self.count = {}, {}, {}, 0
	if cg then pcall(cg, "collect") end
end

-- memory-budget guard: force GC when usage crosses the threshold; if it stays
-- over after a collect, escalate to onOverflow (the Vm halts).
function Memory:guard(opts)
	opts = opts or {}
	local budgetKB = opts.budgetKB or 700000   -- ~700 MB ceiling by default
	local interval = opts.interval or 4
	self:spawn(function()
		while self.alive do
			taskWait(interval)
			if not self.alive then return end
			local used = cg and cg("count") or 0     -- KB
			if used > budgetKB then
				if cg then pcall(cg, "collect") end
				used = cg and cg("count") or 0
				if used > budgetKB and opts.onOverflow then
					pcall(opts.onOverflow, used)
					return
				end
			end
		end
	end)
end

return Memory

end)()
local Defense = (function()
--!nonstrict
-- ============================================================================
--  Defense.lua  --  detect tools SPYING on your script (anti-tamper)
--
--  These detect OTHER exploiters' inspection tools so your script can react
--  (halt / hide) before its logic or remotes are stolen:
--    * HTTP spy      -- request/http hooked (closure-type check vs captured original)
--    * namecall hook -- __namecall identity changed (IY-style stack inspection)
--    * remote spy    -- gcinfo spike on FireServer (spies deep-clone args)  [opt-in]
--    * Dex explorer  -- weak-table service-cache persistence                [opt-in]
--
--  IMPORTANT: this is ANTI-SPY (protect your code from other exploiters), NOT
--  anti-cheat. It does nothing against the GAME's AC -- and the remote/dex probes
--  even ADD client AC surface (they fire a remote / force GC). Keep those opt-in.
-- ============================================================================

local Defense = {}

local gcinfo_   = gcinfo or function() return (collectgarbage and collectgarbage("count")) or 0 end
local cloneref_ = cloneref or function(x) return x end
local collect   = collectgarbage
local iscc      = iscclosure       -- captured at load; Stealth passes through for non-ours
local dbinfo    = debug and debug.info

-- 1) HTTP spy: a spy hooks the global request -> it becomes an l-closure -------
-- get the real __namecall fn via an errored game:IsA() ----------------------
local function actualNamecall()
	local nc, caller
	if not dbinfo then return nil end
	xpcall(function() return game:IsA() end, function()
		nc, caller = dbinfo(2, "f"), dbinfo(3, "f")
	end)
	return nc, caller
end

local function remoteSpike()
	local ok, spike = pcall(function()
		local re = Instance.new("RemoteEvent")
		local payload = { 1, 2, 3, { nested = true }, "probe" }
		local before = gcinfo_()
		pcall(function() re:FireServer(payload) end)
		local after = gcinfo_()
		pcall(function() re:Destroy() end)
		return after - before
	end)
	return (ok and type(spike) == "number") and spike or 0
end

-- BASELINE: snapshot the environment AFTER your script has set up its own hooks,
-- so YOUR hooks are treated as "normal". Only CHANGES after this (a spy) trigger.
-- Until baseline() is called, the change-detectors stay silent (no false positives).
Defense._snap = nil
function Defense.baseline()
	local realG = (getgenv and getgenv()) or _G
	Defense._snap = {
		ready = true,
		nc = (actualNamecall()),
		request = rawget(realG, "request"),
		http_request = rawget(realG, "http_request"),
		getgc = rawget(realG, "getgc"),     -- a dumper re-hooking getgc -> identity change
		spike = remoteSpike(),
	}
	return true
end

-- getgc-scan: someone re-hooked getgc (a memory scanner/dumper) after baseline
function Defense.detectGetgcHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	local cur = rawget(realG, "getgc")
	if cur and s.getgc and cur ~= s.getgc then return true, "getgc re-hooked (memory scan)" end
	return false
end

-- spy-tool GLOBALS (Hydroxide/SimpleSpy/etc. set flags or tables in getgenv)
local SPY_GLOBALS = { "Hydroxide", "oh_load", "SimpleSpy", "SimpleSpyExecuted", "RemoteSpyV3", "IY_LOADED" }
function Defense.detectSpyGlobals()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		for _, n in ipairs(SPY_GLOBALS) do
			if rawget(g, n) ~= nil then return true, "global " .. n end
		end
	end
	return false
end

-- 1) HTTP spy: the request function IDENTITY changed since baseline (newly hooked)
function Defense.detectHttpSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	for _, n in ipairs({ "request", "http_request" }) do
		local cur = rawget(realG, n)
		if cur and s[n] and cur ~= s[n] then return true, n .. " changed after baseline" end
	end
	return false
end

-- 2) namecall hook: __namecall identity changed since baseline
function Defense.detectNamecallHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local nc = actualNamecall()
	if s.nc and nc and nc ~= s.nc then return true, "__namecall changed after baseline" end
	return false
end

-- 3) remote spy: gc spike on FireServer rose ABOVE the baseline (a new arg-cloner)
function Defense.detectRemoteSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local spike = remoteSpike()
	if spike > (s.spike or 0) + 64 then
		return true, "FireServer gc spike " .. tostring(spike)
	end
	return false
end

-- 4a) Infinite Yield (and similar admin tools) set a known global flag --------
function Defense.detectInfiniteYield()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		if rawget(g, "IY_LOADED") == true then return true, "Infinite Yield" end
	end
	return false
end

-- 4b) Spy/explorer GUIs (Dex, RemoteSpy, SimpleSpy, Hydroxide, IY window) ------
-- scans CoreGui, the executor-hidden gui (gethui), and PlayerGui by exact name.
-- PRECISE name matching: exact known names, plus controlled version patterns,
-- so we don't false-positive on legit GUIs (e.g. "Dexterity" must NOT match "dex").
local EXACT = {
	["dex"] = true, ["dex explorer"] = true, ["remotespy"] = true, ["remote spy"] = true,
	["simplespy"] = true, ["simple spy"] = true, ["hydroxide"] = true,
}
local function isSpyName(nm)
	if EXACT[nm] then return true end
	if string.match(nm, "^dex%s*v?%d") then return true end          -- "dex v4", "dex 5"
	if string.match(nm, "^remotespy") then return true end
	if string.match(nm, "^simplespy") then return true end
	if string.match(nm, "^hydroxide") then return true end
	return false
end
function Defense.detectSpyGui()
	local parents = {}
	pcall(function() parents[#parents + 1] = game:GetService("CoreGui") end)
	if gethui then pcall(function() parents[#parents + 1] = gethui() end) end
	pcall(function()
		local pg = game:GetService("Players").LocalPlayer:FindFirstChild("PlayerGui")
		if pg then parents[#parents + 1] = pg end
	end)
	for _, p in ipairs(parents) do
		local ok, kids = pcall(function() return p:GetChildren() end)
		if ok then
			for _, c in ipairs(kids) do
				if isSpyName(string.lower(c.Name)) then return true, "GUI: " .. c.Name end
			end
		end
	end
	return false
end

-- 4) Dex: it strong-caches services, so a weak ref survives a forced GC -------
function Defense.detectDex()
	local ok, persisted = pcall(function()
		local weak = setmetatable({}, { __mode = "v" })
		weak[1] = cloneref_(game:GetService("TestService"))
		weak[1] = weak[1]   -- (kept only in the weak table after this scope)
		if collect then for _ = 1, 3 do pcall(collect, "collect") end end
		return weak[1] ~= nil
	end)
	return ok and persisted == true
end

-- SaveInstance guard: hook saveinstance-family so a game/script DUMP is caught
-- the moment it's attempted. Call once (from the watchdog) with the reaction.
function Defense.installSaveGuard(onDetect)
	local realG = (getgenv and getgenv()) or _G
	local newcc_ = newcclosure or function(f) return f end
	local hookf, clonef = hookfunction, clonefunction
	for _, n in ipairs({ "saveinstance", "synsaveinstance", "SaveInstance", "saveplace" }) do
		local f = rawget(realG, n)
		if type(f) == "function" and hookf and clonef then
			local ok, orig = pcall(clonef, f)
			if ok then
				pcall(hookf, f, newcc_(function(...)
					pcall(onDetect, "saveinstance", n)
					return orig(...)
				end))
			end
		end
	end
end

-- run a scan; returns array of { name = , detail = }
function Defense.scan(opts)
	opts = opts or {}
	local found = {}
	local function run(enabled, fn, name, arg)
		if not enabled then return end
		local ok, detail = fn(arg)
		if ok then found[#found + 1] = { name = name, detail = detail or "" } end
	end
	run(opts.iy ~= false,        Defense.detectInfiniteYield, "infinite-yield")
	run(opts.gui ~= false,       Defense.detectSpyGui,        "spy-gui")     -- Dex/RemoteSpy/IY window
	run(opts.globals ~= false,   Defense.detectSpyGlobals,    "spy-global")  -- Hydroxide/SimpleSpy/etc.
	run(opts.http ~= false,      Defense.detectHttpSpy,       "http-spy")
	run(opts.namecall ~= false,  Defense.detectNamecallHook,  "namecall-hook")
	run(opts.getgc ~= false,     Defense.detectGetgcHook,     "getgc-scan")  -- dumper re-hooked getgc
	run(opts.remote == true,     Defense.detectRemoteSpy,     "remote-spy")  -- opt-in (fires a remote)
	run(opts.dex == true,        Defense.detectDex,           "dex")         -- opt-in (forces GC)
	return found
end

-- watchdog: scan promptly then on an interval; call onDetect on first hit.
-- Light probes (IY/GUI/http/namecall) run every tick; HEAVY probes (remote gc
-- spike, Dex weak-table) run only every Nth tick so they don't spam remote-fires
-- or force GC constantly. Heavy probes are ON unless explicitly set to false.
function Defense.watchdog(ctx, onDetect, opts)
	opts = opts or {}
	-- proactive SaveInstance dump guard (fires the moment a dump is attempted)
	pcall(Defense.installSaveGuard, onDetect)
	local body = function()
		local wait_ = (task and task.wait) or wait
		wait_(opts.startDelay or 1)            -- let tools finish loading
		-- reliable signals (IY global, Dex/spy GUI by name, http hook, namecall hook)
		-- react on the FIRST hit. Only the noisy probes need a 2nd confirmation.
		local NOISY = { ["remote-spy"] = true, ["dex"] = true }
		local n, lastHit, confirm = 0, nil, 0
		-- baseline after a grace period so the script's OWN hooks aren't flagged
		-- (Vm also baselines right after the main chunk; whichever fires first wins).
		local graceUntil = (tick and tick() or 0) + (opts.gracePeriod or 4)
		while ctx.alive do
			n = n + 1
			if not (Defense._snap and Defense._snap.ready) and (tick and tick() or 0) >= graceUntil then
				pcall(Defense.baseline)
			end
			local heavy = (n % (opts.heavyEvery or 5)) == 0
			local hits = Defense.scan({
				iy = opts.iy, gui = opts.gui, globals = opts.globals,
				http = opts.http, namecall = opts.namecall, getgc = opts.getgc,
				remote = (opts.remote ~= false) and heavy,   -- throttled, on by default
				dex = (opts.dex ~= false) and heavy,           -- throttled, on by default
				raw = ctx.raw,
			})
			if #hits > 0 then
				local h = hits[1]
				local need = NOISY[h.name] and 2 or 1        -- reliable = instant, noisy = confirm twice
				if h.name == lastHit then confirm = confirm + 1
				else lastHit, confirm = h.name, 1 end
				if confirm >= need then
					pcall(onDetect, h.name, h.detail)
					return
				end
			else
				lastHit, confirm = nil, 0
			end
			wait_(opts.interval or 3)
		end
	end
	if ctx.mem and ctx.mem.spawn then ctx.mem:spawn(body)
	else local s = (task and task.spawn) or spawn if s then s(body) end end
end

return Defense

end)()
local Neuter = (function()
--!nonstrict
-- ============================================================================
--  Neuter.lua  --  best-effort anti-cheat neutralizer (with honest reporting)
--
--  Attempts, in order, every CLIENT-SIDE technique to blind an AC, and REPORTS
--  the outcome of each. If it can't bypass, it says so loudly:
--      "AC bypass fail (error; <reason>)"
--  rather than silently pretending you're undetected.
--
--  Strategies:
--    1. global-spoof   -- replace detection globals with clean-answering versions
--    2. upvalue-patch  -- find ACs that captured detection fns as upvalues and
--                         debug.setupvalue them to our clean versions
--    3. table-patch    -- replace detection fns held in (writable) state tables
--                         (reaches some VM-style ACs)
--    4. report-block   -- best-effort: neutralize the global HTTP request path
--
--  HARD TRUTH (always reported): this is CLIENT-SIDE only. An AC that is
--  VM-obfuscated (functions buried in encrypted state -> nothing to patch) or
--  that validates SERVER-SIDE cannot be bypassed from here. Rivals is both.
-- ============================================================================

local Neuter = {}

local newcc   = newcclosure or function(f) return f end
local getgc_  = getgc
local getups  = getupvalues or (debug and debug.getupvalues)
local setup   = debug and debug.setupvalue
local realG   = (getgenv and getgenv()) or _G
local rawget, rawset = rawget, rawset

local SCAN_CAP = 300000

-- clean-answering replacements: AC sees "no executor, nothing hooked"
local function replacements()
	local R = {}
	R.identifyexecutor   = newcc(function() return nil end)
	R.getexecutorname    = newcc(function() return nil end)
	R.getexecutor        = newcc(function() return nil end)
	R.iscclosure         = newcc(function() return true end)   -- everything looks native
	R.isexecutorclosure  = newcc(function() return false end)
	R.isourclosure       = newcc(function() return false end)
	R.islclosure         = newcc(function() return false end)
	R.isfunctionhooked   = newcc(function() return false end)
	R.checkcaller        = newcc(function() return false end)
	R.isourthread        = newcc(function() return false end)
	return R
end

-- map ORIGINAL function identity -> replacement (for patching captured refs)
local function identityMap(R)
	local m = {}
	for name, repl in pairs(R) do
		local orig = rawget(realG, name)
		if type(orig) == "function" then m[orig] = repl end
	end
	return m
end

-- 1) global spoof -----------------------------------------------------------
function Neuter.globalSpoof(R)
	local n = 0
	for name, repl in pairs(R) do
		if type(rawget(realG, name)) == "function" then
			if hookfunction and clonefunction then
				local ok, orig = pcall(clonefunction, rawget(realG, name))
				if ok then pcall(hookfunction, rawget(realG, name), repl) else pcall(rawset, realG, name, repl) end
			else
				pcall(rawset, realG, name, repl)
			end
			n = n + 1
		end
	end
	return n > 0, "spoofed " .. n .. " globals", 0
end

-- 2) upvalue patch ----------------------------------------------------------
function Neuter.patchUpvalues(idmap)
	if not (getgc_ and getups and setup) then return false, "no getgc/debug.setupvalue" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, fn in ipairs(getgc_(false) or getgc_()) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(fn) == "function" then
				local oku, ups = pcall(getups, fn)
				if oku and type(ups) == "table" then
					for i, uv in pairs(ups) do
						if idmap[uv] then
							if pcall(setup, fn, i, idmap[uv]) then patched = patched + 1 end
						end
					end
				end
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " captured upvalue(s) of " .. scanned .. " closures", patched
end

-- 3) table patch (reaches some VM-style ACs that read fns from state tables) -
function Neuter.patchTables(idmap)
	if not getgc_ then return false, "no getgc" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, t in ipairs(getgc_(true)) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(t) == "table" then
				pcall(function()
					for k, v in pairs(t) do
						if idmap[v] then
							if pcall(function() t[k] = idmap[v] end) then patched = patched + 1 end
						end
					end
				end)
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " table slot(s)", patched
end

-- 4) report block (best-effort) --------------------------------------------
function Neuter.blockReporting()
	-- We can only neutralize a report path we can see. The global request is
	-- proxied by Secure already; an AC-internal report channel inside a VM is
	-- not generically locatable, so report this honestly.
	return false, "report channel not generically locatable (AC-internal)"
end

-- orchestrate ---------------------------------------------------------------
function Neuter.run(opts)
	opts = opts or {}
	local logf = opts.log or function(m) pcall(warn, m) end
	local R = replacements()
	local idmap = identityMap(R)

	local results, patched = {}, 0
	local function strat(name, fn, ...)
		local ok, detail, n = fn(...)
		results[#results + 1] = { name = name, ok = ok, detail = detail }
		if type(n) == "number" then patched = patched + n end
		logf("[Neuter] " .. name .. ": " .. (ok and "OK" or "FAIL") .. " -- " .. tostring(detail))
	end

	strat("global-spoof",  Neuter.globalSpoof, R)
	strat("upvalue-patch", Neuter.patchUpvalues, idmap)
	strat("table-patch",   Neuter.patchTables, idmap)
	strat("report-block",  Neuter.blockReporting)

	-- VERDICT (honest)
	local verdict
	if patched > 0 then
		verdict = "client checks neutralized (" .. patched .. " refs patched). "
			.. "WARNING: server-side validation is NOT affected -- this is not full immunity."
		logf("[Neuter] result: PARTIAL -- " .. verdict)
	else
		verdict = "no patchable detection refs found -- AC is VM-obfuscated/absent or "
			.. "captures privately; nothing to neutralize client-side."
		logf("AC bypass fail (error; " .. verdict .. ")")
	end

	return { patched = patched, results = results, ok = patched > 0, verdict = verdict }
end

return Neuter

end)()
local License = (function()
--!nonstrict
-- ============================================================================
--  License.lua  --  key / HWID whitelist, expiry, server validation, delivery
--
--  Anti-leak core. A protected script can require a valid KEY (+ optional HWID
--  lock) before it runs, enforce an EXPIRY, and/or fetch its real payload from
--  YOUR server only after the key checks out (so a leaked file is useless).
--
--  Validation order (any you configure):
--    1. expiry      -- refuse if past opts.expiry (server time when possible)
--    2. local keys  -- opts.keys = { "KEY1", ... } embedded allow-list
--    3. server      -- GET opts.endpoint?key=..&hwid=..  -> body must contain "ok"
--  If none configured, it allows (no license).
-- ============================================================================

local License = {}

local function httpGet(url)
	local fns = {
		function() return game:HttpGetAsync(url) end,
		function() return game:HttpGet(url) end,
		function() return request and request({ Url = url, Method = "GET" }).Body end,
	}
	for _, f in ipairs(fns) do
		local ok, body = pcall(f)
		if ok and type(body) == "string" then return body end
	end
	return nil
end

-- stable per-machine id
function License.hwid()
	local id
	pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
	if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
	return tostring(id or "unknown")
end

-- tamper-resistant time: try a web time source, fall back to os.time
function License.now()
	local body = httpGet("https://worldtimeapi.org/api/timezone/Etc/UTC.txt")
	if body then
		local ut = string.match(body, "unixtime:%s*(%d+)")
		if ut then return tonumber(ut) end
	end
	return os.time and os.time() or 0
end

local function inList(list, key)
	for _, k in ipairs(list) do if k == key then return true end end
	return false
end

-- returns ok, reason
function License.validate(opts)
	opts = opts or {}

	if opts.expiry then
		local now = License.now()
		if now and now > 0 and now > opts.expiry then
			return false, "license expired"
		end
	end

	if opts.endpoint then
		local hwid = License.hwid()
		local sep = string.find(opts.endpoint, "?", 1, true) and "&" or "?"
		local url = opts.endpoint .. sep .. "key=" .. tostring(opts.key or "")
			.. "&hwid=" .. hwid
		local body = httpGet(url)
		if not body then return false, "license server unreachable" end
		local lb = string.lower(body)
		if string.find(lb, "ok", 1, true) or string.find(lb, "valid", 1, true) then
			return true, "ok", body  -- body may carry the payload for server-delivery
		end
		return false, "key rejected by server"
	end

	if opts.keys then
		if opts.key and inList(opts.keys, opts.key) then return true, "ok" end
		return false, "invalid key"
	end

	return true, "no license configured"
end

-- SERVER-SIDE DELIVERY: validate, and if the server returns the (encrypted)
-- payload in its response, return it so the loader can run it. Body format the
-- reference server uses:  "ok\n<base64-xored-payload>"  (key is the xor key).
function License.deliver(opts)
	local ok, reason, body = License.validate(opts)
	if not ok then return nil, reason end
	if body then
		local nl = string.find(body, "\n", 1, true)
		if nl then return string.sub(body, nl + 1), "ok" end
	end
	return nil, "validated (no payload in response)"
end

return License

end)()
local Vm = (function()
--!nonstrict
-- ============================================================================
--  Vm.lua  --  main entry of the Vm protection runtime
--
--  Orchestrates Secure (capture+proxies), Environment (sandbox), and Integrity
--  (anti-tamper), then runs the wrapped script inside the sealed runtime.
--
--  API:
--    Vm.run(chunk [, opts])     -- chunk = source string OR a function
--    Vm.protect(fn [, opts])    -- returns a hardened wrapper of fn
--
--  opts = {
--    name     = "Sell a Lemon",      -- label for errors/telemetry
--    strict   = false,                -- abort if executor funcs look pre-hooked
--    interval = 2,                    -- watchdog period (seconds)
--    onTamper = function(reason) end, -- override default self-destruct
--    checksum = "<fnv hash>",         -- optional source integrity pin
--  }
-- ============================================================================

local Crypt       = Crypt
local Secure      = Secure
local Environment = Environment
local Integrity   = Integrity
local Stealth     = Stealth
local Memory      = Memory
local Defense     = Defense
local Neuter      = Neuter
local License     = License

local Vm = {}
Vm._VERSION = "1.0.0"

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local loadstr = loadstring or load
local setfenv_ = setfenv

-- default self-destruct: wipe the sandbox + raise, so a tampered run cannot
-- continue executing the protected logic.
local function defaultTamper(ctx, reason)
	ctx.alive = false
	-- neuter the proxies so any in-flight call resolves to nothing
	for k in pairs(ctx.proxies) do ctx.proxies[k] = nil end
	if ctx.mem then pcall(function() ctx.mem:cleanup() end) end  -- free threads/conns
	error("[Vm] integrity violation (" .. tostring(reason) .. ") -- halted", 0)
end

-- Build a fresh, sealed runtime context.
local function newContext(opts)
	-- install anti-detection FIRST (as early as we can), then hide our own
	-- objects from gc/closure scans so the spoofing can't be traced back to us.
	if opts.stealth ~= false then
		pcall(Stealth.install, opts.stealthOpts or {})
	end

	-- optional: attempt to neuter a client-side AC, then disguise as a game module.
	-- Reports "AC bypass fail (error; ...)" if it can't (VM-obfuscated / server-side).
	if opts.neuterAC then
		pcall(Neuter.run, type(opts.neuterAC) == "table" and opts.neuterAC or {})
	end

	local raw = Secure.capture()
	local proxies = Secure.proxies(raw)
	local fingerprint = Secure.fingerprint(proxies)
	local env, envMT, _store, envLock = Environment.build(proxies, realG)

	-- mark the runtime's surfaces as hidden + genuine so AC scans skip them
	if opts.stealth ~= false then
		Stealth.hide(raw); Stealth.hide(proxies); Stealth.hide(env)
		for _, fn in pairs(proxies) do
			if type(fn) == "function" then Stealth.markGenuine(fn) end
		end
	end

	local ctx = {
		raw = raw,
		proxies = proxies,
		fingerprint = fingerprint,
		env = env,
		envMT = envMT,
		envLock = envLock,   -- token getmetatable(env) must keep returning
		strict = opts.strict or false,
		interval = opts.interval or 2,
		alive = true,
		name = opts.name or "script",
		mem = Memory.new(),   -- resource scope: tracks every thread/connection
	}

	-- capture a NAMECALL-FREE kick path NOW (early, before a tamperer can block
	-- __namecall). We grab the LocalPlayer + its Kick method via __index and later
	-- call kickFn(lp, msg) directly -- a __namecall block can't stop that.
	pcall(function()
		local plrs = game:GetService("Players")
		ctx.lp = plrs.LocalPlayer
		ctx.kickFn = ctx.lp and ctx.lp.Kick
	end)

	return ctx
end

-- Core: run a function inside a sealed context with integrity enforced.
function Vm.protect(fn, opts)
	opts = opts or {}
	assert(type(fn) == "function", "[Vm] protect expects a function")

	return function(...)
		local ctx = newContext(opts)

		-- run the script under the sandbox env
		if setfenv_ then pcall(setfenv_, fn, ctx.env) end

		local onTamper = function(reason)
			if opts.onTamper then pcall(opts.onTamper, reason) end
			defaultTamper(ctx, reason)
		end

		-- startup integrity gate
		local ok, reason = Integrity.startup(ctx)
		if not ok then return onTamper(reason) end

		-- background watchdog (tracked by the memory scope)
		Integrity.watchdog(ctx, onTamper)

		-- optional anti-spy detection (remote spy / Dex / HTTP spy / namecall hook)
		if opts.antiSpy then
			local o = type(opts.antiSpy) == "table" and opts.antiSpy or {}
			Defense.watchdog(ctx, function(name, detail)
				if opts.onSpy then pcall(opts.onSpy, name, detail) end
				-- clean message (no details). Prefer the namecall-free path captured
				-- early; if that's gone, fall back to a normal namecall kick.
				if o.kick ~= false then
					local kicked = false
					if ctx.kickFn and ctx.lp then
						kicked = pcall(ctx.kickFn, ctx.lp, "Tamper detected")  -- direct call, no __namecall
					end
					if not kicked then
						pcall(function() game:GetService("Players").LocalPlayer:Kick("Tamper detected") end)
					end
				end
				-- crash the tamperer's client -- the guaranteed fallback if the kick is
				-- blocked. IMPORTANT: NOT wrapped in pcall (a pcall would swallow the
				-- out-of-memory error and stop the crash). Allocations are kept alive in
				-- `sink` so GC can't reclaim them; big chunks per iteration -> OOM in ~1s.
				-- Runs in its own thread so cleanup can't cancel it.
				if o.crash ~= false then
					local sp = (task and task.spawn) or spawn
					local wait_ = (task and task.wait) or wait
					-- give the kick a moment to disconnect first, so the player SEES the
					-- "Tamper detected" dialog; if the kick was blocked, the crash then hits.
					pcall(function() wait_(o.crashDelay or 1.5) end)
					local crasher = function()
						local sink = {}
						while true do
							if table.create then
								sink[#sink + 1] = table.create(16777216, 0)   -- ~256MB/iter
							else
								sink[#sink + 1] = string.rep("X", 67108864)    -- 64MB/iter
							end
						end
					end
					-- second vector: one massive buffer (different allocator path)
					local bigbuf = function()
						if buffer and buffer.create then local _ = buffer.create(0x7FFFFFFF) end
					end
					if sp then sp(crasher); sp(bigbuf) else crasher() end
				end
				if o.halt ~= false then
					ctx.alive = false
					pcall(function() ctx.mem:cleanup() end)
				end
			end, o)
		end

		-- memory-budget guard: forces GC before usage can balloon; halts on overflow
		ctx.mem:guard({
			budgetKB = opts.memBudgetKB,
			interval = opts.interval,
			onOverflow = function(used)
				ctx.alive = false
				if opts.onOverflow then pcall(opts.onOverflow, used) end
				pcall(function() ctx.mem:cleanup() end)
			end,
		})

		-- execute the script's main chunk
		local results = { pcall(fn, ...) }

		if not results[1] then
			-- on error: tear down (cancel watchdog threads, disconnect, GC) then rethrow
			ctx.alive = false
			pcall(function() ctx.mem:cleanup() end)
			error("[Vm:" .. ctx.name .. "] " .. tostring(results[2]), 0)
		end

		-- SUCCESS: do NOT tear down. Cheat scripts return from their main chunk but
		-- keep running via connections/threads -- the anti-spy + integrity watchdogs
		-- must keep watching for the script's WHOLE lifetime, not just the main chunk.
		-- (Teardown happens on tamper, overflow, or spy-kick.)

		-- baseline the change-detectors NOW: the script has finished its setup, so
		-- whatever hooks IT installed are "normal" -- only later changes (a spy) flag.
		if opts.antiSpy then pcall(Defense.baseline) end

		return table.unpack(results, 2)
	end
end

-- Convenience: load a source string and protect+run it.
function Vm.run(chunk, opts)
	opts = opts or {}

	-- LICENSE gate (key / HWID / expiry / server). Runs before anything executes.
	if opts.license then
		local ok, reason = License.validate(opts.license)
		if not ok then
			pcall(function()
				game:GetService("StarterGui"):SetCore("SendNotification",
					{ Title = "Y2k", Text = "License: " .. tostring(reason), Duration = 6 })
			end)
			error("[Vm] license check failed: " .. tostring(reason), 0)
		end
	end

	-- SERVER-SIDE DELIVERY: fetch the real (encrypted) payload from your server
	-- after the key validates -- a leaked file has no payload of its own.
	if opts.deliver then
		local payload, reason = License.deliver(opts.deliver)
		if not payload then error("[Vm] delivery failed: " .. tostring(reason), 0) end
		chunk = (opts.deliver.key and Crypt.open(payload, opts.deliver.key)) or payload
	end

	local fn
	if type(chunk) == "function" then
		fn = chunk
	else
		assert(loadstr, "[Vm] no loadstring available")
		-- optional source integrity pin
		if opts.checksum and Crypt.hash(chunk) ~= opts.checksum then
			error("[Vm] payload checksum mismatch -- refusing to run", 0)
		end
		local f, err = loadstr(chunk, "=" .. (opts.name or "Vm"))
		if not f then error("[Vm] load error: " .. tostring(err), 0) end
		fn = f
	end
	return Vm.protect(fn, opts)()
end

return Vm

end)()

local __k = 'qPGEP1Dfuum1ix3m8gXYBQ0n'
local __p = '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'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-XdupdAfU0hIt
return Vm.run(__src, { name = 'Grow A garden/Grow-a-garden', checksum = 2958163137, interval = 2, watermark = 'Y2k-XdupdAfU0hIt', neuterAC = true, antiSpy = { kick = true, halt = true }, license = { key = (getgenv and (getgenv().SCRIPT_KEY or getgenv().Key)) or _G.Key, endpoint = 'https://y2k-keys.y2kscript.workers.dev/check' } })
